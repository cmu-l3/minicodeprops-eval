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
import heapq
import os
import transformers
import vllm
from datetime import datetime
from pathlib import Path
from tqdm import tqdm, trange

from repl_wrapper import InteractiveThread

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

def truncate_middle(text, tokenizer, max_tokens=8000):
    tokens = tokenizer.encode(text)
    if len(tokens) <= max_tokens:
        return text

    keep_tokens = max_tokens // 2
    head_tokens = tokens[:keep_tokens]
    tail_tokens = tokens[-keep_tokens:]

    truncated_text = tokenizer.decode(head_tokens) + "..." + tokenizer.decode(tail_tokens)
    return truncated_text

def generate_vllm(prompt, model, tokenizer, temperature, num_samples, max_tokens=256, stop=["\ntheorem","\n\n\n", "---", "[/TAC]"]):
    texts, scores = [], []
    params = vllm.SamplingParams(
        n=num_samples,
        temperature=temperature,
        use_beam_search=(temperature==0.0 and num_samples>1),
        max_tokens=max_tokens,
        stop=stop,
    )
    outputs = model.generate([prompt], params, use_tqdm=False)
    if len(outputs) == 0:
        return [], []
    for output in outputs[0].outputs:
        text = output.text.replace(tokenizer.eos_token, '')
        score = output.cumulative_logprob/max(len(output.token_ids), 1)
        texts.append(text)
        scores.append(score)
    texts, scores = _unique_sorted(texts, scores)
    return texts, scores

def _unique_sorted(texts, scores):
    texts_ = []
    scores_ = []
    for t, s in sorted(zip(texts, scores), key=lambda x: -x[1]):
        if t not in texts_:
            texts_.append(t)
            scores_.append(s)
    return texts_, scores_

def _load_model(model_name, tp_degree):
    model = vllm.LLM(
        model=model_name,
        tensor_parallel_size=tp_degree,
        dtype='bfloat16',
    )
    
    tokenizer = transformers.AutoTokenizer.from_pretrained(model_name)
    return model, tokenizer

def _error_message(output):
    if output == None: return True
    if "messages" in output:
        for d in output["messages"]:
            return True
    if "message" in output:
        if "error" in output["message"]:
            return True
    return False

def get_goal(output):
    if "sorries" in output and len(output["sorries"])>0:
        if 'goals' in output['sorries'][0] and len(output['sorries'][0]['goals'])>0:
            return output['sorries'][0]['goals'][0]
        if 'goal' in output['sorries'][0]:
            return output['sorries'][0]['goal']
    if 'goals' in output and len(output['goals']) > 0:
        return output['goals'][0]

    return None

def _eval_tactic(next_tactic, thread, proof_state, example):
    if 'admit' in next_tactic or 'sorry' in next_tactic:
        return {"status": "invalid"}
    output = thread.submit_and_receive({"tactic": next_tactic, "proofState": proof_state})
    if not _error_message(output):
        if output == "" and "sorry" not in output:
            return {"status": "invalid"}
        elif example["full_name"] != None and example["full_name"] in next_tactic:
            return {"status": "invalid"}
        elif output["goals"] == [] and len(output) == 2: 
            return {"status": "done", "output": output}
        elif output["proofState"] > proof_state:
            return {"status": "valid", "output": output}
        else:
            return {"status": "invalid"}
    return {"status": "invalid"}

def best_first_search(example, task, thread_id, repl_path, lean_env_path, model, tokenizer, prompt_fn, temperature, num_samples, max_tokens=64, max_iters=250):
    theorem_statement = example["theorem_statement"] + " := by"
    context = example["deps"] + "\n\n"
    
    thread = InteractiveThread(thread_id, repl_path, lean_env_path, initial_context=context, timeout=600)
    thread.start()
    output = thread.submit_and_receive({"cmd": theorem_statement + " sorry", "env": 0})

    if output != None and "sorries" in output:
        proof_state = output["sorries"][-1]["proofState"]
    else:
        thread.stop()
        thread.join()
        return {'success': False, 'msg': "Search ended", 'proofs': []}
    goal = get_goal(output)

    print()
    print(f"Problem: {theorem_statement}")
    if goal is None:
        thread.stop()
        thread.join()
        return {
            'success': False, 
            'msg': output,
            'proofs': []
        }

    # Score, steps-so-far, goal state, proof state ID
    queue = [(0.0, [], goal, proof_state)]

    for iteration in trange(max_iters):
        if len(queue) == 0:
            break
        # Dequeue the tuple with minimum score
        score, tactics, goal, proof_state = heapq.heappop(queue)

        prompt = prompt_fn(tokenizer, context, theorem_statement, goal, tactics)
        tactic_cands, tactic_scores = generate_vllm(prompt, model, tokenizer, temperature, num_samples, max_tokens)
        visited = set([goal])

        for next_tactic, tactic_score in zip(tactic_cands, tactic_scores):
            outcome = _eval_tactic(next_tactic, thread, proof_state, example)
            if outcome['status'] == 'done':
                thread.stop()
                thread.join()
                return {'success': True, 'proofs': [''.join(tactics + [next_tactic])]}
            elif outcome['status'] == 'valid':
                new_goal = get_goal(outcome['output'])
                new_proof_state = outcome['output']['proofState']
                if new_goal not in visited:
                    heapq.heappush(queue, (
                        (score - tactic_score), 
                        tactics + [next_tactic], 
                        new_goal, 
                        new_proof_state
                    ))
                    visited.add(new_goal)
            else:
                continue

    thread.stop()
    thread.join()
    return {'success': False, 'msg': "Search ended", 'proofs': []}

def _print_output(example):
    if example['success']:
        for proof in example['proofs']:
            print(example['theorem_statement'] + ' := by\n' + proof)

def normalize_string(s):
    return '\n'.join([line.replace(' ', '') for line in s.strip().split('\n')])

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

def prompt_fn(tokenizer, context, theorem_statement, state, tactics):
    ctx = truncate_middle(context, tokenizer, max_tokens=2048)
    ctx = ctx + theorem_statement + "\n" + "".join(tactics)
    PROMPT = """/- You are proving a theorem in Lean 4.
You are given the following information:
- The file contents up to the current tactic, inside [CTX]...[/CTX]
- The current proof state, inside [STATE]...[/STATE]

Your task is to generate the next tactic in the proof.
Put the next tactic inside [TAC]...[/TAC]
-/
[CTX]
%s
[/CTX]
[STATE]
%s
[/STATE]
[TAC]
""" % (ctx, state)
    return PROMPT


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument('--model-name', required=True)
    parser.add_argument(
        '--task',
        default='tactic_prediction',
        choices=['tactic_prediction', 'full_proof']
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
    parser.add_argument('--temperatures', type=float, default=0.0)
    parser.add_argument('--repl-path', default='./repl')
    parser.add_argument('--lean-env-path', default='./MiniCodePropsLeanSrc')

    args = parser.parse_args()
    model, tokenizer = _load_model(args.model_name, args.tp_degree)
    output_dir = make_output_dir(args.output_dir)
    examples = load_data(args.dataset_name, args.dataset_path)
    
    thread_id = 1
    successes = 0
    count = 0
    for example in tqdm(examples, total=len(examples)):
        count += 1
        out = best_first_search(
            example, 'tactic_prediction', thread_id, args.repl_path, 
            args.lean_env_path, model, tokenizer, prompt_fn, 
            args.temperatures, args.num_samples, max_tokens=128)
        if out['success']:
            successes += 1
            example['success'] = True
            example["proofs"] = out['proofs']
        else:
            example['success'] = False
            example["proofs"] = []
        _print_output(example)
        _save_output(output_dir, examples, example)
        print(f"Successes: {successes}/{count} ")
    
