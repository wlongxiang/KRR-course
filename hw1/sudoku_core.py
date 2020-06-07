###
### Propagation function to be used in the recursive sudoku solver
###
from itertools import chain


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
def solve_sudoku_SAT(sudoku, k):
    return None


###
### Solver that uses CSP encoding
###
def solve_sudoku_CSP(sudoku, k):
    return None


###
### Solver that uses ASP encoding
###
def solve_sudoku_ASP(sudoku, k):
    return None


###
### Solver that uses ILP encoding
###
def solve_sudoku_ILP(sudoku, k):
    return None
