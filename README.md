# minicodeprops-eval

This repository contains evaluation scripts for:
*[miniCodeProps: a Minimal Benchmark for Proving Code Properties](https://arxiv.org/abs/2406.11915)*
```
@misc{lohn2024minicodepropsminimalbenchmarkproving,
      title={miniCodeProps: a Minimal Benchmark for Proving Code Properties}, 
      author={Evan Lohn and Sean Welleck},
      year={2024},
      eprint={2406.11915},
      archivePrefix={arXiv},
      primaryClass={cs.SE},
      url={https://arxiv.org/abs/2406.11915}, 
}
```

## Setup instructions (adapted from [minictx-eval](https://github.com/cmu-l3/minictx-eval))

## Requirements

- Python 3
- PyTorch
- Required Python packages (specified in `requirements.txt`)

  ```bash
  pip install -r requirements.txt
  ```

- Lean 4


## Setup Environment

1. **Install Lean 4**

   If you are running Linux, you need only install elan following [these instructions](https://leanprover-community.github.io/install/linux.html). There is no need to install a code editor
   (i.e. no need to follow the instructions to install VS-code). To ensure your path is updated, you should run `source $HOME/.elan/env` as prompted by the installer
   If you are evaluating in an environment with vscode, follow the instructions on the [Lean 4 installation page](https://leanprover.github.io/lean4/doc/quickstart.html) to set up Lean 4.
   

2. **Set up and build your target Lean project**

   ```bash
   cd MiniCodePropsLeanSrc
   lake exe cache get
   lake build
   ```

3. **Set up and build Lean REPL**

   Build the REPL project (we include a copy of the REPL in the `/repl` directory of this repository with a suitable Lean version):

   ```bash
   cd repl
   lake build
   ```

## Running the Evaluation

### Edit the Script

Open a script in the `script/` directory and verify that the paths and parameters are correctly set according to your setup. The script contains the following variables:

- `TASK`: The task name (e.g. `full_proof`).
- `MAX_ITERS`: The maximum number of iterations (default: `100`).
- `NUM_SAMPLES`: The number of samples (default: `32`).
- `TEMPERATURES`: The temperatures for sampling (default: `0.0`).
- `DATASET`: The name of the dataset (default: `minicodeprops`).
- `DATA`: The path to the dataset file (default: `data/minicodeprops_bench_ps.jsonl`).
- `MODEL`: The model name (default: `gpt-4o`).
- `NAME`: The name for the output directory.
- `OUTPUT_DIR`: The directory where the output will be saved.
- `REPL_PATH`: The path to the REPL project.
- `LEAN_PATH`: The path to the Lean project environment.

### Run the Script

Make the script executable and run it:

```bash
chmod +x script/gpt4.sh
./script/gpt4.sh
```

```bash
chmod +x script/bfs.sh
./script/bfs.sh
```

### Output

The output will be saved in the `${OUTPUT_DIR}` directory.

## `repl_wrapper.py`

The evaluation code interacts with the Lean compiler using the Lean REPL. `repl_wrapper.py` provides a Python interface to interact with the Lean REPL directly.

### Usage

Create a new thread by calling `InteractiveThread(thread_id, repl_path, lean_env_path)`, where:

- `thread_id`: Any number
- `repl_path`: The path to the REPL directory
- `lean_env_path`: The path to the Lean project containing the environment you want to test

Example:

```python
from repl_wrapper import InteractiveThread

thread = InteractiveThread(1, repl_path, lean_env_path)
thread.start()

cmd = {'cmd': 'import MiniF2F.Minif2fImport\n  open BigOperators Real Nat Topology'}
output = thread.submit_and_receive(cmd)

thread.close()
thread.join()
```

`thread.submit_and_receive` takes a dictionary as input and returns the output of the REPL in a dictionary.


## Credits

The implementation adapts the [minictx-eval](https://github.com/cmu-l3/minictx-eval) repo from:
*[miniCTX: Neural Theorem Proving with (Long-)Contexts](https://www.arxiv.org/abs/2408.03350)*
```
@misc{hu2024minictxneuraltheoremproving,
      title={miniCTX: Neural Theorem Proving with (Long-)Contexts}, 
      author={Jiewen Hu and Thomas Zhu and Sean Welleck},
      year={2024},
      eprint={2408.03350},
      archivePrefix={arXiv},
      primaryClass={cs.AI},
      url={https://arxiv.org/abs/2408.03350}, 
}
```
