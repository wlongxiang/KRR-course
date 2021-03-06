###
### Propagation function to be used in the recursive sudoku solver
###
import time
from itertools import chain

import clingo
from pysat.formula import CNF
from pysat.solvers import MinisatGH


def deep_copy(sudoku_possible_values):
    copy = []
    for row in sudoku_possible_values:
        row_copy = []
        for element in row:
            element_copy = element.copy()
            row_copy.append(element_copy)
        copy.append(row_copy)
    return copy


### Pretty printing representation
def pretty_repr(sudoku, k):
    repr = ""
    numwidth = len(str(k ** 2))

    def pretty_line(k):
        return "+" + "+".join(["-" * ((numwidth + 1) * k + 1)] * k) + "+\n"

    # Add a line separator at the beginning
    repr += pretty_line(k)
    rownum = 0
    # Go through all rows of the sudoku
    for i in range(0, k):
        for j in range(0, k):
            # Add a row of the sudoku
            repr += "| "
            for u in range(0, k):
                for v in range(0, k):
                    if sudoku[rownum][u * k + v] != 0:
                        repr += str(sudoku[rownum][u * k + v]).zfill(numwidth) + " "
                    else:
                        repr += " " * numwidth + " "
                repr += "| "
            repr += "\n"
            rownum += 1
        # Add a line separator after every k'th row
        repr += pretty_line(k)
    # Return the constructed string (without trailing '\n')
    return repr[:-1]


def propagate(sudoku_possible_values, k):
    """
    In the propogate function, we try to prune values to narrow down the search space.

    :param sudoku_possible_values: the original search space
    :param k: the size of the sudoku
    :return: the pruned search space
    """
    # 1. let's first scan once to find out indice for all single values
    # 2. we loop over all those indices, then eliminating across rows, cols, and blocks for each one
    all_single_vals_positions = {}  # key is (i,j), value is value
    for i in range(k ** 2):
        for j in range(k ** 2):
            possibilities = sudoku_possible_values[i][j]
            if len(possibilities) == 1:
                all_single_vals_positions[(i, j)] = possibilities[0]
    for (i, j), value in all_single_vals_positions.items():
        # remove duplicate values row-wise
        # skip the row that contains the value
        for row_i in chain(range(0, i), range(i + 1, k ** 2)):
            if value in sudoku_possible_values[row_i][j]:
                sudoku_possible_values[row_i][j].remove(value)
        # remove duplicate values col-wise
        for col_j in chain(range(0, j), range(j + 1, k ** 2)):
            if value in sudoku_possible_values[i][col_j]:
                sudoku_possible_values[i][col_j].remove(value)
        # pruning block-wise cells
        # find out which block is it in
        block_i = (i // k) * k
        block_j = (j // k) * k
        # loop over all cells in the block
        for i2 in range(k):
            for j2 in range(k):
                i_b = block_i + i2
                j_b = block_j + j2
                if i != i_b and j != j_b:
                    if value in sudoku_possible_values[i_b][j_b]:
                        sudoku_possible_values[i_b][j_b].remove(value)
    return sudoku_possible_values


###
### Solver that uses SAT encoding
###

# some uti functions first
def var_number(i, j, d, k):
    """
    Convert possible values into propositional vars

    :param i: row number 1 - 9
    :param j: col number 1 - 9
    :param d: digit 1 - 9
    :param k: size of suduko
    :return: variable number 1- 729
    """
    return (k ** 2 * k ** 2) * (i - 1) + (k ** 2) * (j - 1) + d


def extract_digit_from_solution(i, j, solution, k):
    # return the digit of cell i, j according to the solution
    for d in range(1, k ** 2 + 1):
        if var_number(i, j, d, k) in solution:
            return d


def create_clauses(sudoku, k):
    clauses = []
    for i in range(1, k ** 2 + 1):
        for j in range(1, k ** 2 + 1):
            # 1. make sure all cells have at least one one digit
            clauses.append([var_number(i, j, d, k) for d in range(1, k ** 2 + 1)])
            # 2. make sure all cells have only one digit
            for d in range(1, k ** 2 + 1):
                for d2 in range(d + 1, k ** 2 + 1):
                    clauses.append([-var_number(i, j, d, k), -var_number(i, j, d2, k)])

    def add_distinct_clauses(cells):
        """
        Given a list of positions, such as indices for first row, [(1,1), (1,2)... (1,9)]
        we create clauses that make sure each digit is distinct
        """
        for i in range(len(cells)):
            for j in range(i + 1, len(cells)):
                for d in range(1, k ** 2 + 1):
                    clauses.append([-var_number(cells[i][0], cells[i][1], d, k),
                                    -var_number(cells[j][0], cells[j][1], d, k)])

    # make sure each row has distinct value
    for i in range(1, k ** 2 + 1):
        rowwise_cells = [(i, j) for j in range(1, k ** 2 + 1)]
        add_distinct_clauses(rowwise_cells)
    # make sure each col has distinct value
    for j in range(1, k ** 2 + 1):
        colwise_cells = [(i, j) for i in range(1, k ** 2 + 1)]
        add_distinct_clauses(colwise_cells)
    # make sure each block has distinct value
    for i in [1 + n * k for n in range(k - 1)]:  # 1,4,7 when k=3; 1 ,5, 9, 13 when k=4
        for j in [1 + n * k for n in range(k - 1)]:
            add_distinct_clauses([(i + m % k, j + m // k) for m in range(k ** 2)])
    # make sure the prefilled values are honored by a unit clause
    for i in range(1, k ** 2 + 1):
        for j in range(1, k ** 2 + 1):
            d = sudoku[i - 1][j - 1]
            if d > 0:
                clauses.append([var_number(i, j, d, k)])
    return clauses


def solve_sudoku_SAT(sudoku, k):
    #############
    # this solution is adjusted from https://github.com/taufanardi/sudoku-sat-solver/blob/master/Sudoku.py
    # what I have done differently:
    # 1. Adjusted so that it can generate to k-sized problem, not just hardcoded k=3 in the original post
    # 2. Refactored the code to make it more readable and splitted into smaller functions instead of chunk of code
    # 3. Rewrited the `add_distinct_clauses` code to make it more robust and easy to understand
    #############
    # make clauses
    clauses = create_clauses(sudoku, k)
    # append clauses to formula
    formula = CNF()
    for c in clauses:
        formula.append(c)
    # solve the SAT problem
    solver = MinisatGH()
    solver.append_formula(formula)
    answer = solver.solve()
    if not answer:
        return None
    # get the solution
    solution = solver.get_model()
    # reformat the solution into a suduko representation
    for i in range(1, k ** 2 + 1):
        for j in range(1, k ** 2 + 1):
            sudoku[i - 1][j - 1] = extract_digit_from_solution(i, j, solution, k)
    return sudoku


###
### Solver that uses CSP encoding
###
from ortools.sat.python import cp_model


def solve_sudoku_CSP(sudoku, k):
    ###########################
    # this solution only references the or-tool documentation and the provided example
    # it follows the same structure of the SAT solver, which is inspired by a existing solution as shown above
    model = cp_model.CpModel()
    # create variables with domain contrstrain, x1_1... x9_9 all in (1 to 9)
    vars = dict()
    for i in range(1, k ** 2 + 1):
        for j in range(1, k ** 2 + 1):
            vars[(i, j)] = model.NewIntVar(1, k ** 2, "x{}_{}".format(i, j))

    # make sure all row values are distinct
    def add_distinct_constrain(cells):
        """
        Given a list of positions, such as indices for first row, [(1,1), (1,2)... (1,9)]
        we create clauses that make sure each digit is distinct
        """
        all_vars = [vars[i] for i in cells]
        model.AddAllDifferent(all_vars)

    # make sure each row has distinct value
    for i in range(1, k ** 2 + 1):
        rowwise_cells = [(i, j) for j in range(1, k ** 2 + 1)]
        add_distinct_constrain(rowwise_cells)
    # make sure each col has distinct value
    for j in range(1, k ** 2 + 1):
        colwise_cells = [(i, j) for i in range(1, k ** 2 + 1)]
        add_distinct_constrain(colwise_cells)
    # make sure each block has distinct value
    for i in [1 + n * k for n in range(k - 1)]:  # 1,4,7 when k=3; 1 ,5, 9, 13 when k=4
        for j in [1 + n * k for n in range(k - 1)]:
            add_distinct_constrain([(i + m % k, j + m // k) for m in range(k ** 2)])
    # make sure the prefilled values are honored by a unit clause
    for i in range(1, k ** 2 + 1):
        for j in range(1, k ** 2 + 1):
            d = sudoku[i - 1][j - 1]
            if d > 0:
                model.Add(vars[(i, j)] == d)
    solver = cp_model.CpSolver()
    answer = solver.Solve(model)
    if answer == cp_model.FEASIBLE:
        for (i, j), var in vars.items():
            sudoku[i - 1][j - 1] = solver.Value(var)
        return sudoku
    else:
        return None


###
### Solver that uses ASP encoding
###
def solve_sudoku_ASP(sudoku, k):
    ##############
    # The solution is inspired by this blog:
    # https://ddmler.github.io/asp/2018/07/10/answer-set-programming-sudoku-solver.html
    # what I changed:
    # 1. Generated the solution from k=3 to any k
    # 2. Add the prefilled contrains
    # 3. Rewroten the callback function to return the final sudoku in expected format
    ###############
    asp_code = f"""
    x(1..{k ** 2}).
    y(1..{k ** 2}).
    n(1..{k ** 2}).
    
    {{sudoku(X,Y,N): n(N)}}=1 :- x(X) ,y(Y).
    
    subgrid(X,Y,A,B) :- x(X), x(A), y(Y), y(B),(X-1)/{k} == (A-1)/{k}, (Y-1)/{k} == (B-1)/{k}.
    
    :- sudoku(X,Y,N), sudoku(A,Y,N), X!=A.
    :- sudoku(X,Y,N), sudoku(X,B,N), Y!=B.
    :- sudoku(X,Y,V), sudoku(A,B,V), subgrid(X,Y,A,B), X != A, Y != B.
    """
    # Make prefilled values constrains
    for i in range(k ** 2):
        for j in range(k ** 2):
            if sudoku[i][j] != 0:
                v = int(sudoku[i][j])
                # setting the lower bound of prefilled variable to 1, meaning "true" or already assigned.
                asp_code += f"sudoku({i + 1},{j + 1},{v}). "
    control = clingo.Control()
    control.add("base", [], asp_code)
    control.ground([("base", [])])

    def on_model(model):
        for x in model.symbols(shown=True):
            if x.name == "sudoku":
                sudoku[x.arguments[0].number - 1][x.arguments[1].number - 1] = x.arguments[2].number

    control.configuration.solve.models = 0
    answer = control.solve(on_model=on_model)
    if answer.satisfiable == True:
        return sudoku
    else:
        return None


###
### Solver that uses ILP encoding
###
import gurobipy as gp
from gurobipy import GRB


def solve_sudoku_ILP(sudoku, k):
    ################
    # adjusted from this solution: https://www.gurobi.com/documentation/9.0/examples/sudoku_py.html
    # changes I made:
    # 1. Rewritten the constrains to a easy to understand loop, orginally it is a more concise generator form
    # 2. Broke the python generator comprehension syntax for explit loops to make it clearer
    # 3. Added code to reconstruct the sudoku solution to the expected list of list form
    # 4. Expanded solution to use k
    # 5. added extra comments to make the solution clean
    ################
    # each var represents a bool var indicating if at (i, j ) a digit is true
    model = gp.Model('sudoku')
    vars = model.addVars(k ** 2, k ** 2, k ** 2, vtype=GRB.BINARY, name='G')
    # Each cell must take only one value
    for i in range(k ** 2):
        for j in range(k ** 2):
            model.addConstr(vars.sum(i, j, '*') == 1, name="CELL")
    # Each value appears once per row
    for i in range(k ** 2):
        for v in range(k ** 2):
            model.addConstr(vars.sum(i, '*', v) == 1, name='ROWWISE')
    # Each value appears once per column
    for j in range(k ** 2):
        for v in range(k ** 2):
            model.addConstr(vars.sum('*', j, v) == 1, name="COLWISE")
    # Each value appears once per block
    for v in range(k ** 2):
        for i0 in range(k):
            for j0 in range(k):
                # make the sum constrain for each block
                sum_list = []
                for i in range(i0 * k, (i0 + 1) * k):
                    for j in range(j0 * k, (j0 + 1) * k):
                        sum_list.append(vars[i, j, v])
                model.addConstr(gp.quicksum(sum_list) == 1, name="BLOCK")
    # Make prefilled values constrains
    for i in range(k ** 2):
        for j in range(k ** 2):
            if sudoku[i][j] != 0:
                v = int(sudoku[i][j]) - 1
                # setting the lower bound of prefilled variable to 1, meaning "true" or already assigned.
                vars[i, j, v].LB = 1
    model.optimize()
    # the model results are stored in the X attribute in gurobi
    solution = model.getAttr('X', vars)
    res_final = []
    for i in range(k ** 2):
        sol = []
        for j in range(k ** 2):
            for v in range(k ** 2):
                if solution[i, j, v] > 0.5:
                    sol.append(int(v + 1))
        res_final.append(sol)
    return res_final
