"""Adapted from:

https://github.com/cmu-l3/minictx-eval

@misc{hu2024minictxneuraltheoremproving,
      title={miniCTX: Neural Theorem Proving with (Long-)Contexts}, 
      author={Jiewen Hu and Thomas Zhu and Sean Welleck},
      year={2024},
      eprint={2408.03350},
      archivePrefix={arXiv},
      primaryClass={cs.AI},
      url={https://arxiv.org/abs/2408.03350}, 
}

Authors: Jiewen Hu, Sean Welleck
"""
import json
import subprocess
import os
import re
import openai
import tempfile
import tiktoken
from datetime import datetime
from pathlib import Path
from tqdm import tqdm

openai.api_key = os.environ['OPENAI_API_KEY']  

os.environ["TOKENIZERS_PARALLELISM"] = "true"  

def load_data(dataset_name, dataset_path):
    if 'minicodeprops' in dataset_name:
        data = []
        with open(dataset_path) as f:
            for line in f.readlines():
                data_ = json.loads(line)
                data_['theorem_statement'] = data_['prop_defn'].split(':=')[0]
                data.append(data_)
    return data

def make_refinement_prompt(context, results):
    attempts = ""
    for result in results:
        attempts += (
            "=== ATTEMPT ===\n%s\n--- Errors ---\n%s\n" % (
                result['proof'],
                str(result['errors'][0])[:1024]
            )
        )
    PROMPT = """/- You are proving a theorem in Lean 4.
You are given the following information:
- The file contents up to the current tactic, inside [CTX]...[/CTX]
- Your prior proof attempts, along with their error messages, inside [ATTEMPT]...[/ATTEMPT]

Your task is to generate a correct proof.
Learn from the prior attempts, and either refine a proof, try a different approach, or synthesize ideas.
Put the generation inside [PROOF]...[/PROOF].
If you find it helpful, you can precede the proof with brief thoughts inside [THOUGHTS]...[/THOUGHTS]
In summary, your output should be of the form:
[THOUGHTS]
...
[/THOUGHTS]
[PROOF]
...
[/PROOF]
Your proof will be checked by Lean. Therefore, make sure there are
no additional comments or text, and DO NOT include := by in your proof.
-/
[CTX]
""" + context + """
[/CTX]
[ATTEMPT]
""" + attempts + """
[/ATTEMPT]
"""
    return PROMPT

def make_prompt(context):
    PROMPT = """/- You are proving a theorem in Lean 4.
You are given the following information:
- The file contents up to the current tactic, inside [CTX]...[/CTX]

Your task is to generate the rest of the proof.
Put the generation inside [PROOF]...[/PROOF].
If you find it helpful, you can precede the proof with brief thoughts inside [THOUGHTS]...[/THOUGHTS]
In summary, your output should be of the form:
[THOUGHTS]
...
[/THOUGHTS]
[PROOF]
...
[/PROOF]
Your proof will be checked by Lean. Therefore, make sure there are
no additional comments or text, and DO NOT include := by in your proof.
-/
[CTX]
""" + context + """
[/CTX]
"""
    return PROMPT

def remove_last_comment(ctx):
    pattern = r'/--[^/]*?-/(\n*)$'
    ctx = re.sub(pattern, '', ctx, flags=re.DOTALL)
    return ctx

def _no_banned_words(response):
    if 'sorry' in response:
        return False
    if 'admit' in response:
        return False
    return True

def check(imports, theorem_statement, response, repl_path, lean_env_path):
    with tempfile.NamedTemporaryFile(mode='w+', delete=False) as temp:
        json.dump({"cmd": remove_last_comment(imports)}, temp, ensure_ascii=False)
        temp.write("\n\n")
        json.dump({"cmd": theorem_statement + response, "env": 0}, temp, ensure_ascii=False)
        temp.write("\n\n")
        temp.flush()
        temp_name = temp.name
    
    command = f'lake env ../{repl_path}/.lake/build/bin/repl < {temp_name}'
    try:
        result = subprocess.run(command, shell=True, capture_output=True, text=True, cwd=lean_env_path, timeout=60)
        result_dict = result.stdout.split("\n\n")
        env = json.loads(result_dict[0])
        output = json.loads(result_dict[1])

    except:
        return {
            "success": False,
            "proof": response,
            "errors": ["Exception"]
        }
    if env == None: 
        return {
            "success": False,
            "proof": None,
            "errors": ["Env"]
        }
    env_error = []
    if "messages" in env:
        env_error = env["messages"]

    no_error = True
    if "messages" in output:
        errors = [message for message in output["messages"] if message not in env_error]
        for message in errors:
            if message["severity"] == 'error':
                no_error = False
    if 'env' in output and no_error and _no_banned_words(response): 
        return {
            "success": True,
            "proof": response,
            "errors": []
        }
    return {
        "success": False,
        "proof": response,
        "errors": errors
    }

def truncate_middle(text, max_tokens=8000):
    tokens = enc.encode(text)
    
    if len(tokens) <= max_tokens:
        return text  
    
    half_max_tokens = max_tokens // 2
    head_tokens = tokens[:half_max_tokens]
    tail_tokens = tokens[-half_max_tokens:]
    
    truncated_text = enc.decode(head_tokens) + " ... " + enc.decode(tail_tokens)
    
    return truncated_text

def generate_api(prompt, model, temperatures, num_samples, max_tokens=512):
    texts, scores = [], []
    for temperature in temperatures:
        responses = openai.chat.completions.create(
            model=model,
            messages=[
                {"role": "system", "content": "You are a helpful assistant who is an expert in the Lean theorem prover."},
                {"role": "user", "content": prompt}
            ],
            max_tokens=max_tokens,
            temperature=temperature,
            n=num_samples
        )
        for choice in responses.choices:
            texts.append(choice.message.content)
            scores.append(0)

    return texts, scores

def _prompt(theorem_statement, ctx):
    new_ctx = truncate_middle(ctx)
    prompt = make_prompt(new_ctx + theorem_statement)
    return prompt

def process_responses_GPT4o(responses):
    responses_ = []
    for response in responses:
        try:
            response = response.split('[PROOF]')[1].split('[/PROOF]')[0]
        except IndexError:
            pass
        responses_.append(response)
    responses = list(set(responses))
    return responses_

def evaluation_API(example, thread_id, repl_path, lean_env_path, model, prompt_fn, temperature, num_samples, max_tokens=1024, early_stop=True, num_refinement=1):
    theorem_statement = example["theorem_statement"] + " := by\n"
    
    context = example["deps"] + '\n'
    prompt = prompt_fn(theorem_statement, context)
    responses, _ = generate_api(prompt, model, [temperature], num_samples, max_tokens)
    responses = process_responses_GPT4o(responses)
    results = []
    for response in responses:
        result = check(context, theorem_statement, response, repl_path, lean_env_path)
        results.append(result)
        if early_stop and result['success']:
            break
    
    for i in range(num_refinement):
        if not any([x['success'] for x in results]):
            new_ctx = truncate_middle(context)
            prompt = make_refinement_prompt(new_ctx + theorem_statement, results)
            responses, _ = generate_api(prompt, model, [temperature], num_samples, max_tokens)
            responses = process_responses_GPT4o(responses)
            results = []
            for response in responses:
                result = check(context, theorem_statement, response, repl_path, lean_env_path)
                results.append(result)
                if result['success']:
                    result['refinement'] = i+1
                    print("====Successful refinement@%d!!!====" % (i+1))
                    break

    success = any([x['success'] for x in results])
    return results, success

def _print_output(example):
    if example['success']:
        for proof in example['proofs']:
            print(example['theorem_statement'] + ' := by\n' + proof)

def make_output_dir(output_dir):
    dt = datetime.now().strftime("%d-%m-%Y-%H-%M")
    output_dir = os.path.join(output_dir, dt)
    Path(output_dir).mkdir(parents=True, exist_ok=True)
    Path(os.path.join(output_dir, 'success')).mkdir(parents=True, exist_ok=True)
    return output_dir

def _save_output(output_dir, results, example):
    with open(os.path.join(output_dir, 'results.jsonl'), 'w') as f:
        for result in results:
            f.write(json.dumps(result))
            f.write('\n')
    
    if example['success']:
        for i, proof in enumerate(example['proofs']):
            with open(os.path.join(output_dir, 'success', '%s_%d.txt' % (example['full_name'], i)), 'w') as f:
                f.write(example['deps'] + '\n')
                f.write(example['theorem_statement'] + ' := by\n')
                f.write(proof)

def get_full_name(statement):
    word_list = statement.split()
    for i in range(len(word_list)):
        if "theorem" in word_list[i] or "lemma" in word_list[i]:
            return statement.split()[i+1]
    return None

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument('--model-name', required=True)
    parser.add_argument(
        '--task',
        default='full_proof',
        choices=['full_proof']
    )
    parser.add_argument(
        '--dataset-name',
        default='minicodeprops'
    )
    parser.add_argument('--dataset-path', default='data/minicodeprops_bench_ps.jsonl')
    parser.add_argument('--output-dir', default='output/minicodeprops')
    parser.add_argument('--tp-degree', type=int, default=1)
    parser.add_argument('--max-iters', type=int, default=100)
    parser.add_argument('--num-samples', type=int, default=32)
    parser.add_argument('--temperatures', type=float, default=0.7)
    parser.add_argument('--repl-path', default='./repl')
    parser.add_argument('--lean-env-path', default='./MiniCodePropsLeanSrc')

    args = parser.parse_args()

    enc = tiktoken.encoding_for_model(args.model_name) 
    model = args.model_name
    evaluation = evaluation_API

    output_dir = make_output_dir(args.output_dir)
    examples = load_data(args.dataset_name, args.dataset_path)
    
    prompt_fn = _prompt
    thread_id = 1

    successes = 0
    count = 0
    for example in tqdm(examples, total=len(examples)):
        count += 1
        results, success = evaluation(
            example, thread_id, 
            args.repl_path, args.lean_env_path, 
            model, prompt_fn, 
            args.temperatures, args.num_samples
        )
        if success:
            successes += 1
            example['success'] = True
            example['proofs'] = [x['proof'] for x in results if x['success']]
            example['refinements'] = [x['refinement'] for x in results if 'refinement' in x]
        else:
            example['success'] = False
            example["proofs"] = []
            example['refinements'] = []
        _print_output(example)
        _save_output(output_dir, examples, example)
        print(f"Successes: {successes}/{count} ")
    
