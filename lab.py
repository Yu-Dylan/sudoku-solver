"""
6.101 Lab 8:
SAT Solver
"""

#!/usr/bin/env python3

import sys
import typing

sys.setrecursionlimit(10_000)
# NO ADDITIONAL IMPORTS


def assign_value(formula, assignments):
    """
    Assign assignments in the formula.
    """
    new_formula = []
    for clause in formula:
        new_clause = []
        for tup in clause:
            if tup[0] in assignments:
                if tup[1] == assignments[tup[0]]:
                    new_clause = []
                    break
                elif len(clause) == 1:
                    return None
            else:
                new_clause.append(tup)
        if len(new_clause) > 0:
            new_formula.append(new_clause)
    return new_formula


def reduce_formula(formula, assignments):
    """
    Given assignments, reduce the formula.
    """

    def reduce_helper(form, assign):
        """
        Helper to reduce formula.
        """
        if form is None:
            return None
        if len(form) == 0:
            return form
        for clause in form:
            if len(clause) == 1:
                tup = clause[0]
                assign[tup[0]] = tup[1]
                form = assign_value(form, assign)
                if form is None:
                    del assign[tup[0]]
                    return None
                return reduce_helper(form, assign)
        return form

    formula = assign_value(formula, assignments)
    if formula is None:
        return None
    return reduce_helper(formula, assignments)


# def remove_irrelevancies(formula):
#     """
#     Removes irrelevant clauses with a variable being both True and False.
#     """
#     print(formula)
#     print("  ")
#     new_formula = []
#     for clause in formula:
#         bo = True
#         for var in clause:
#             opp_var = (var[0], not var[1])
#             if opp_var in clause:
#                 bo = False
#                 break
#         if bo:
#             new_formula.append(clause)
#     print(new_formula)
#     print("==")
#     return new_formula

def satisfying_assignment(formula):
    """
    Find a satisfying assignment for a given CNF formula.
    Returns that assignment if one exists, or None otherwise.
    """
    if formula is None:
        return None
    if len(formula) == 0:
        return {}
    # formula = remove_irrelevancies(formula)
    for bo in [True, False]:
        assignments = {formula[0][0][0]: bo}
        new_formula = reduce_formula(formula, assignments)
        if new_formula is None:
            continue
        new_assignments = satisfying_assignment(new_formula)
        if new_assignments is not None:
            assignments.update(new_assignments)
            return assignments
    return None


def sudoku_board_to_sat_formula(sudoku_board):
    """
    Generates a SAT formula that, when solved, represents a solution to the
    given sudoku board.  The result should be a formula of the right form to be
    passed to the satisfying_assignment function above.
    """

    def cell_value(row, col, val, bo):
        return ((row, col, val), bo)

    board_length = len(sudoku_board)

    def formula_0(length):
        # must match initial values
        formula0 = []
        for row in range(length):
            for col in range(length):
                formula0.append([cell_value(row, col, sudoku_board[row][col], True)])
        return formula0

    def formula_1(length):
        # every cell has at least 1 value
        formula1 = []
        for row in range(length):
            for col in range(length):
                rule = []
                for val in range(1, length + 1):
                    rule.append(cell_value(row, col, val, True))
                formula1.append(rule)
        return formula1

    def formula_2(length):
        # every cell has at most 1 value
        formula2 = []
        for row in range(length):
            for col in range(length):
                for val1 in range(1, length):
                    for val2 in range(val1 + 1, length + 1):
                        rule = []
                        rule.append(cell_value(row, col, val1, False))
                        rule.append(cell_value(row, col, val2, False))
                        formula2.append(rule)
        return formula2

    def formula_3(length):
        # no 2 cells in the same row are the same value
        formula3 = []
        for row in range(length):
            for col1 in range(length - 1):
                for col2 in range(col1, length):
                    for val in range(1, length + 1):
                        rule = []
                        rule.append(cell_value(row, col1, val, False))
                        rule.append(cell_value(row, col2, val, False))
                        formula3.append(rule)
        return formula3

    def formula_4(length):
        # no 2 cells in the same col are the same value
        formula4 = []
        for row1 in range(length - 1):
            for row2 in range(row1, length):
                for col in range(length):
                    for val in range(1, length + 1):
                        rule = []
                        rule.append(cell_value(row1, col, val, False))
                        rule.append(cell_value(row2, col, val, False))
                        formula4.append(rule)
        return formula4

    def formula_5(length):
        # no 2 cells in the same subgrid are the same value
        formula5 = []
        block_length = int(length**0.5)
        for block_row in range(block_length):
            for block_col in range(block_length):
                for row1 in range(
                    block_row * block_length, (block_row + 1) * block_length
                ):
                    for col1 in range(
                        block_col * block_length, (block_col + 1) * block_length
                    ):
                        for row2 in range(
                            block_row * block_length, (block_row + 1) * block_length
                        ):
                            for col2 in range(
                                block_col * block_length, (block_col + 1) * block_length
                            ):
                                for val in range(1, board_length + 1):
                                    if (row1 != row2) or (col1 != col2):
                                        rule = []
                                        rule.append(cell_value(row1, col1, val, False))
                                        rule.append(cell_value(row2, col2, val, False))
                                        formula5.append(rule)
        return formula5

    formulas = (
        formula_0(board_length)
        + formula_1(board_length)
        + formula_2(board_length)
        + formula_3(board_length)
        + formula_4(board_length)
        + formula_5(board_length)
    )
    return formulas


def assignments_to_sudoku_board(assignments, n):
    """
    Given a variable assignment as given by satisfying_assignment, as well as a
    size n, construct an n-by-n 2-d array (list-of-lists) representing the
    solution given by the provided assignment of variables.

    If the given assignments correspond to an unsolvable board, return None
    instead.
    """

    def make_board(size):
        """
        Make an empty board.
        """
        board = []
        for _ in range(size):
            board.append([0] * size)
        return board

    if assignments is None:
        return None
    sudoku_board = make_board(n)
    for key in assignments:
        if assignments[key]:
            if sudoku_board[key[0]][key[1]] > 0:
                return None
            else:
                sudoku_board[key[0]][key[1]] = key[2]
    return sudoku_board

if __name__ == "__main__":
    pass
