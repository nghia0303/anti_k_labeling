An exact approach for solving no-hole anti-k-labeling of graphs
============================================== 
## Project Structure

### Core Components
- `data/hb/`: Contains input data.
- `code/`: Contains code for all baselines and the methods presented in the paper.
- `logs/`: Contains logs for each method.
- `output/`: Contains generated output files.
- `result/`: Contains compacted Excel result files.

## Requirements

### Python
- Python 3.9-3.12
- Install the required libraries:
```bash
pip install -r requirements.txt
```

### <a href="https://github.com/lip6/painless/tree/master">Painless Solver</a>

#### Prerequisites
- C++20-compatible compiler (GCC recommended)
- [Boost Library](https://www.boost.org/) headers
- [OpenMPI](https://www.open-mpi.org/) implementation
- Standard build tools (make, autoconf)
- POSIX-compatible environment

#### Build Instructions
1. Clone the repository:
   ```bash
   git clone https://github.com/lip6/painless
   cd painless
   ```

2. Build the entire project:
   ```bash
   make
   ```

### CPLEX Solver

#### Free version
```bash
pip install cplex
pip install docplex
```
This version is limited and can only be used with small datasets.

#### Full version
Install the full CPLEX runtime from <a href="https://www.ibm.com/products/ilog-cplex-optimization-studio">IBM ILOG CPLEX Optimization Studio</a>.

### Gurobi Solver

#### Free version
```bash
pip install gurobipy
```
This version includes a size-limited license and can only be used with small datasets (up to 2,000 variables and 2,000 constraints).

#### Full version
Install the full Gurobi Optimizer and activate your Academic License from <a href="https://www.gurobi.com/product">Gurobi Optimizer Overview</a>.

## How to Run the Code
Run a specific script:
```bash
python code/<method_name>.py
```
Logs will be written to `logs/<method_name>/`, and outputs will be written to `output/<method_name>/`.
