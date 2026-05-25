import glob
import multiprocessing
import os
import time
import logging
from pysat.card import CardEnc
from pysat.pb import PBEnc
from pysat.solvers import Solver
import pandas as pd
import subprocess
import shutil
from typing import Optional, Dict, Any


#  ./painless/build/release/painless_release cnf/K_n117_k80/K_n117_k80_w38.cnf   -c=4   -solver=cckk -no-model

# Global config
name = "PSE"
LOG_FILE = "logs/PSE/log_" + name + ".txt" # Where to save log file
EXCEL_FILE = "output/PSE/output_" + name + ".xlsx" # Where to save Excel file (output file)

# --- Painless runner config ---
PAINLESS_BIN = "./painless/build/release/painless_release"  # painless binary path
PAINLESS_ARGS = ["-c=4", "-solver=ccck"]       # Painless args
RUN_PAINLESS = True # Run Painless solver or not

top_id = 2

# ----------------------------- Logging setup -----------------------------
RESULT_LEVEL_NUM = 25
logging.addLevelName(RESULT_LEVEL_NUM, "RESULT")

def result(self, msg, *args, **kwargs):
    if self.isEnabledFor(RESULT_LEVEL_NUM):
        self._log(RESULT_LEVEL_NUM, msg, args, **kwargs)

logging.Logger.result = result
def setup_logger(name: str = "akl", log_file: str = LOG_FILE, level=logging.INFO) -> logging.Logger:
    logger = logging.getLogger(name)
    if getattr(logger, "_configured", False):
        return logger

    logger.setLevel(level)
    logger.propagate = False
    
    for h in list(logger.handlers):
        logger.removeHandler(h)

    fmt = logging.Formatter("%(asctime)s | %(levelname)s | %(processName)s | %(message)s")

    fh = logging.FileHandler(log_file, encoding="utf-8")
    fh.setLevel(level)
    fh.setFormatter(fmt)
    logger.addHandler(fh)

    logger._configured = True  # type: ignore[attr-defined]
    return logger
# ------------------------------------------------------------------------


def solve_no_hole_anti_k_labeling(graph, k, width, queue, timeout_sec=1800, instance_name="A" ):
    logger = setup_logger()
    start = time.time()
    global top_id
    top_id = 2

    solver = Solver(name='Cadical195')
    clauses = [[-1]]
    n = len(graph)
    x = [[1]]
    for i in range(1, n + 1):
        tmp = [1]
        for j in range(1, k + 1):
            tmp.append(top_id)
            top_id += 1
        x.append(tmp)
        
    logger.info(f"Number of clauses before symmetry breaking: {len(clauses)}")
    clauses.extend(Symetry_breaking(graph, x, k))
    logger.info(f"Number of clauses after symmetry breaking: {len(clauses)}")
    
    L = [[1]]
    for i in range(1, n + 1):
        tmp = [1]
        for j in range(1, k + 1):
            tmp.append(top_id)
            top_id += 1
        L.append(tmp)

    # Link x and L
    for i in range(1, n + 1):
        xx = [1]
        LL = [1]
        for label in range(1, k + 1):
            xx.append(x[i][label])
            LL.append(L[i][label])
        clauses.extend(SCL_AMO(xx, LL, k))


    for label in range(1, k + 1):
        clause = []
        for i in range(1, n + 1):
            clause.append(x[i][label])

        clauses.extend(AtLeastOne(clause))

    for u in graph:
        for v in graph[u]:
            for labelu in range(1, k + 1):
                minv = max(0, labelu - width)
                maxv = min(k + 1, labelu + width)
                if minv == 0 and maxv == k + 1:
                    clauses.append([-x[u][labelu]])
                    continue
                if minv == 0:
                    clauses.append([-x[u][labelu], -L[v][labelu + width - 1]])
                if maxv == k + 1:
                    clauses.append([-x[u][labelu], L[v][labelu - width]])
                if minv > 0 and maxv < k + 1:
                    clauses.append([-x[u][labelu], L[v][labelu - width], -L[v][labelu + width - 1]])


            for labelv in range(1, k + 1):
                minu = max(0, labelv - width)
                maxu = min(k + 1, labelv + width)
                if minu == 0 and maxu == k + 1:
                    clauses.append([-x[v][labelv]])
                    continue
                if minu == 0:
                    clauses.append([-x[v][labelv], -L[u][labelv + width - 1]])
                if maxu == k + 1:
                    clauses.append([-x[v][labelv], L[u][labelv - width]])
                if minu > 0 and maxu < k + 1:
                    clauses.append([-x[v][labelv], L[u][labelv - width], -L[u][labelv + width - 1]])
                    

    solver.append_formula(clauses)

    logger.info(f"Number of variables: {solver.nof_vars()}")
    logger.info(f"Number of clauses: {solver.nof_clauses()}")
    logger.info(f"Real nums of clauses: {len(clauses)}")
    logger.info(f"Real nums of variables: {top_id - 2}")

    queue.put(top_id - 2)
    queue.put(len(clauses))

    cnf_path = write_cnf_to_file(clauses, solver, n, k, width, instance_name)

    if RUN_PAINLESS and cnf_path:
        try:
            painless_timeout = min(1800, timeout_sec)
        except NameError:
            painless_timeout = 1800

        pres = run_painless(cnf_path, timeout_sec=painless_timeout)
        logger.result(f"[PAINLESS] result: status={pres['status']} time={pres['time_sec']:.2f}s rc={pres['returncode']}")

        if pres["status"] == "SAT":
            ok, msg = validate_from_painless(
                pres["stdout"], graph, x, n, k, width
            )
            logger.result(f"[VALIDATE][PAINLESS] {ok} | {msg}")

            if not ok:
                logger.error("INVALID MODEL FROM PAINLESS")
                return False

            queue.put(True)
            return True

        elif pres["status"] == "UNSAT":
            queue.put(False)
            logger.result(f"[PAINLESS] Shortcut: UNSAT at width={width}")
            end = time.time()
            logger.result(f"Time taken: {end - start} seconds")
            return False

    # If Painless fails or is disabled, solve with PySAT
    logger.error("Some thing wrong with PAINLESS, Solving with PySAT...")

    if solver.solve():
        model = solver.get_model()
        ok, msg = validate_from_pysat_model(
            model, graph, x, n, k, width
        )
        logger.result(f"[VALIDATE][PYSAT] {ok} | {msg}")

        if not ok:
            logger.error("INVALID MODEL FROM PYSAT")
            return False

        queue.put(True)
        return True

    else:
        queue.put(False)
        logger.result("No solution exists")
        end = time.time()
        logger.result(f"Time taken: {end - start} seconds")
        return False



def SCL_AMO(x, R, k):
    # x <=> order
    # x1 <= 1 <=> R1
    # x1 + x2 <= 1 <=> R2
    # x1 + x2 + x3 <= 1 <=> R3
    # x1 + x2 + x3 + x4 <= 1 <=> R4

    clauses = []
    
    for index in range(1, k + 1):
        clauses.append([-x[index], R[index]])

    for index in range(1, k):
        clauses.append([-R[index], R[index + 1]])

    clauses.append([x[1], -R[1]])

    for index in range(2, k + 1):
        clauses.append([x[index], R[index-1], -R[index]])

    for index in range(2, k + 1):
        clauses.append([-x[index], -R[index-1]])

    clauses.append([R[k]])
    
    return clauses


def Symetry_breaking(graph, x, k):
    cnt = [0] * (len(graph) + 1)
    for u in graph:
        for v in graph[u]:
            cnt[u] += 1
            cnt[v] += 1

    node = 1
    for i in range(1, len(cnt)):
        if node == -1 or cnt[i] < cnt[node]:
            node = i

    clause = []
    for label in range(k//2 + 1, k+1):
        clause.append([-x[node][label]])
    return clause


def AtLeastOne(variables):
    global top_id

    enc = CardEnc.atleast(
        lits=variables,
        bound=1,
        encoding=1,
        top_id=top_id
    )
    top_id = enc.nv

    return enc.clauses


# ======================= VALIDATION MODULE =======================

def parse_dimacs_model(stdout: str):
    """
    Parse DIMACS model from solver output
    """
    true_lits = set()
    for line in stdout.splitlines():
        line = line.strip()
        if not line or line[0] != 'v':
            continue
        parts = line.split()[1:]
        for lit in parts:
            if lit == '0':
                continue
            lit = int(lit)
            if lit > 0:
                true_lits.add(lit)
    return true_lits


def extract_labels_from_model(model_true_lits, x, n, k):
    """
    Extract label_of from model
    """
    label_of = {}

    for i in range(1, n + 1):
        assigned = False
        for label in range(1, k + 1):
            if x[i][label] in model_true_lits:
                label_of[i] = label
                assigned = True
                break
        if not assigned:
            return None, f"Vertex {i} has no label"

    return label_of, "OK"


def validate_solution(graph, label_of, k, width):
    """
    Validate result solution
    """
    n = len(graph)

    # 1. Exactly-one
    if label_of is None or len(label_of) != n:
        return False, "Not all vertices labeled"

    # 2. No-hole:
    used_labels = set(label_of.values())
    for l in range(1, k + 1):
        if l not in used_labels:
            return False, f"No-hole violated: label {l} unused"

    # 3. Anti-k-labeling constraint
    for u in graph:
        for v in graph[u]:
            if abs(label_of[u] - label_of[v]) < width:
                return False, (
                    f"Width violated on edge ({u},{v}): "
                    f"|{label_of[u]} - {label_of[v]}| < {width}"
                )

    return True, "VALID SOLUTION"


def validate_from_painless(stdout, graph, x, n, k, width):
    """
    Validate output from Painless
    """
    model_true = parse_dimacs_model(stdout)
    label_of, msg = extract_labels_from_model(model_true, x, n, k)
    if label_of is None:
        return False, msg
    return validate_solution(graph, label_of, k, width)


def validate_from_pysat_model(model, graph, x, n, k, width):
    """
    Validate output from PySAT / CaDiCaL
    """
    model_true = {lit for lit in model if lit > 0}
    label_of, msg = extract_labels_from_model(model_true, x, n, k)
    if label_of is None:
        return False, msg
    return validate_solution(graph, label_of, k, width)


# ======================= END VALIDATION MODULE =======================

def read_input(file_path):
    graph = {}
    with open(file_path, 'r') as file:
        n, e, k, lb, ub = map(int, file.readline().split())
        for i in range(1, n + 1):
            graph[i] = []
        for _ in range(e):
            u, v = map(int, file.readline().split())
            graph[u].append(v)
    return graph, k, lb, ub


def run_test_with_timeout(graph, k, width, timeout_sec=3600, instance_name="A"):
    logger = setup_logger()
    global res2

    start = time.time()
    queue = multiprocessing.Queue()

    p = multiprocessing.Process(
        target=solve_no_hole_anti_k_labeling,
        args=(graph, k, width, queue, timeout_sec, instance_name)
    )
    p.start()
    p.join(timeout=timeout_sec)

    if p.is_alive():
        p.terminate()
        p.join()

    num_var = queue.get() if not queue.empty() else None
    num_clause = queue.get() if not queue.empty() else None
    verdict = queue.get() if not queue.empty() else None
    res2.extend([num_var, num_clause, verdict])

    elapsed = round((time.time() - start), 2)

    if verdict is True:
        logger.info(f"Found a solution {width}")
        logger.info(f"[Test k={k}, w={width}] Time: {elapsed} seconds")
        return True
    else:
        logger.info(f"No solution found {width}")
        logger.info(f"[Test k={k}, w={width}] Time: {elapsed} seconds")
        return False


res = [["filename", "n", "k", "lower_bound",
        "upper_bound", "width", "num_vars", "num_clauses", "verdict", "time"]]
res2 = []


def solve_for_ans(graph, k, lower_bound, upper_bound, file, timeout_sec=1800):
    logger = setup_logger()
    global res, res2

    res.append([None, None, None, None, None, None, None, None, None, None])
    time_left = timeout_sec
    ans = -9999
    width = lower_bound

    while True:
        time_start = time.time()
        res2.extend([file, len(graph), k, lower_bound, upper_bound, width])

        if run_test_with_timeout(graph, k, width, time_left, file[0]):
            res2.append(round(time.time() - time_start, 2))
            res.append(res2)
            
            if len(res) == 2:
                write_to_excel(res, mode='write')
            else:
                write_to_excel([res[-1]], mode='append')
            
            res2 = []

            time_left -= time.time() - time_start
            ans = width
            width += 1

            if time_left <= 0.5 or ans == upper_bound:
                if ans == -9999:
                    return -9999
                return -ans
        else:
            res2.append(round(time.time() - time_start, 2))
            res.append(res2)
            
            if len(res) == 2:
                write_to_excel(res, mode='write')
            else:
                write_to_excel([res[-1]], mode='append')
            
            res2 = []

            time_left -= time.time() - time_start
            if time_left <= 0.5:
                if ans == -9999:
                    return -9999
                return -ans
            break

    return ans

def run_painless(cnf_path: str,
                 bin_path: str = PAINLESS_BIN,
                 extra_args=None,
                 timeout_sec: int = 1800,
                 cwd: Optional[str] = None) -> Dict[str, Any]:
    """
    Run Painless solver on given CNF file.
      {
        "status": "SAT"|"UNSAT"|"UNKNOWN"|"TIMEOUT"|"ERROR",
        "time_sec": float,
        "returncode": int | None,
        "stdout": str,
        "stderr": str,
        "cmd": [..]
      }
    """
    logger = setup_logger()
    if extra_args is None:
        extra_args = PAINLESS_ARGS

    exists = os.path.exists(bin_path)
    in_path = shutil.which(bin_path) is not None
    if not exists and not in_path:
        logger.error(f"Painless binary not found: {bin_path}")
        return {"status": "ERROR", "time_sec": 0.0, "returncode": None,
                "stdout": "", "stderr": f"Binary not found: {bin_path}", "cmd": []}

    cmd = [bin_path] + list(extra_args) + [cnf_path]
    t0 = time.time()
    logger.info(f"[PAINLESS] Running: {' '.join(cmd)}")

    try:
        cp = subprocess.run(
            cmd,
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=timeout_sec
        )
        dt = time.time() - t0
        out, err = cp.stdout, cp.stderr
        rc = cp.returncode

        if rc == 10 or "s SATISFIABLE" in out:
            status = "SAT"
        elif rc == 20 or "s UNSATISFIABLE" in out:
            status = "UNSAT"
        elif rc == 0:
            status = "UNKNOWN"
        else:
            status = "ERROR"

        logger.info(f"[PAINLESS] status={status} rc={rc} time={dt:.2f}s")
        if err.strip():
            logger.info(f"[PAINLESS][stderr] {err.strip().splitlines()[-1]}")

        return {"status": status, "time_sec": dt, "returncode": rc,
                "stdout": out, "stderr": err, "cmd": cmd}

    except subprocess.TimeoutExpired:
        dt = time.time() - t0
        logger.info(f"[PAINLESS] TIMEOUT after {dt:.2f}s")
        return {"status": "TIMEOUT", "time_sec": dt, "returncode": None,
                "stdout": "", "stderr": "", "cmd": cmd}
    except Exception as ex:
        dt = time.time() - t0
        logger.exception("[PAINLESS] Exception while running solver")
        return {"status": "ERROR", "time_sec": dt, "returncode": None,
                "stdout": "", "stderr": str(ex), "cmd": cmd}


def solve():
    logger = setup_logger()
    # clear file at start
    with open(LOG_FILE, "w", encoding="utf-8"):
        pass

    # clear Excel file at start
    if os.path.exists(EXCEL_FILE):
        os.remove(EXCEL_FILE)
        logger.info(f"Cleared existing Excel file: {EXCEL_FILE}")

    logger.info("=== Start solve() ===")

    folder_path = "data/hb"
    files = glob.glob(f"{folder_path}/*")

    lst = []
    filename = []

    for file in files:
        lst.append(os.path.join(folder_path, os.path.basename(file)))
        filename.append(os.path.basename(file))

    for i in range(0, len(lst)): # Choose how many files to run by changing the range

        time_start = time.time()
        graph, k, lb, ub = read_input(lst[i])
        file = filename[i]
        ans = -9999
        time_limit = 1800

        ans = solve_for_ans(graph, k, lb, ub, file, time_limit)

        logger.info("$$$$")
        logger.info(str(ans))
        logger.info("$$$$")

        time_end = time.time()
        logger.info(f"Time taken for {file} with k = {k}: {time_end - time_start} seconds")

        if ans >= 0:
            logger.info(f"Maximum width for {file} is {ans}")
        else:
            if ans == -9999:
                logger.info(f"No answer before timeout for {file}")
            else:
                logger.info(f"Maximum width before timeout for {file} is {-ans}")
            logger.info("time out")
    


def write_cnf_to_file(clauses, solver, n, k, width, instance_name="A"):
    """
    Write SAT solver clauses to a CNF file in DIMACS format.
    Returns the path to the CNF file.
    """
    logger = setup_logger()
    base_path = "cnf/v2"
    folder_path = os.path.join(base_path, f"{instance_name}_n{n}_k{k}")

    if not os.path.exists(folder_path):
        os.makedirs(folder_path)

    cnf_filename = os.path.join(folder_path, f"{instance_name}_n{n}_k{k}_w{width}.cnf")

    try:
        with open(cnf_filename, "w", encoding="utf-8") as f:
            f.write(f"p cnf {solver.nof_vars()} {len(clauses)}\n")
            for clause in clauses:
                f.write(" ".join(map(str, clause)) + " 0\n")
        logger.info(f"CNF written to {cnf_filename}")
        return cnf_filename
    except Exception:
        logger.exception("Failed to write CNF")
        return None

def write_to_excel(data, output_file=EXCEL_FILE, mode='write'):
    logger = setup_logger()
    try:
        df = pd.DataFrame(data)
        if mode == 'append' and os.path.exists(output_file):
            existing_df = pd.read_excel(output_file)
            df = pd.concat([existing_df, df], ignore_index=True)
        df.to_excel(output_file, index=False)
        logger.info(f"Data {mode} to {output_file}")
    except Exception:
        logger.exception("Error writing to Excel")


if __name__ == "__main__":
    solve()
