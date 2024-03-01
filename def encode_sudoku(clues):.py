def encode_sudoku(clues):
    # Generate the list of variables
    variables = []
    for i in range(1, 10):
        for j in range(1, 10):
            for k in range(1, 10):
                variables.append((i, j, k))

    # Create the initial set of clauses
    clauses = []

    # Each cell must have exactly one number
    for i in range(1, 10):
        for j in range(1, 10):
            cell_variables = []
            for k in range(1, 10):
                cell_variables.append((i, j, k))
            clauses.extend(exactly_one(cell_variables))

    # Each row must have each number exactly once
    for i in range(1, 10):
        for k in range(1, 10):
            row_variables = []
            for j in range(1, 10):
                row_variables.append((i, j, k))
            clauses.extend(exactly_one(row_variables))

    # Each column must have each number exactly once
    for j in range(1, 10):
        for k in range(1, 10):
            column_variables = []
            for i in range(1, 10):
                column_variables.append((i, j, k))
            clauses.extend(exactly_one(column_variables))

    # Each subgrid must have each number exactly once
    for a in range(0, 3):
        for b in range(0, 3):
            for k in range(1, 10):
                subgrid_variables = []
                for i in range(1, 4):
                    for j in range(1, 4):
                        subgrid_variables.append((3*a+i, 3*b+j, k))
                clauses.extend(exactly_one(subgrid_variables))

    # Encode the given clues
    for i in range(1, 10):
        for j in range(1, 10):
            if clues[i-1][j-1] != 0:
                k = clues[i-1][j-1]
                for m in range(1, 10):
                    if m != k:
                        clauses.append((-variable(i, j, m)))
                clauses.append(variable(i, j, k))
    print(clauses)
    # Convert the clauses to the CNF format
    cnf = ""
    for clause in clauses:
        for literal in clause:
            cnf += str(variable_index(literal)) + " "
        cnf += "0\n"

    return cnf


def variable(i, j, k):
    # Map the (i, j, k) tuple to a variable number
    return (i-1)*81 + (j-1)*9 + k


def variable_index(literal):
    # Map the literal to a variable index in the CNF format
    if literal < 0:
        return -literal*2 - 1
    else:
        return literal*2


def exactly_one(variables):
    # Generate clauses to ensure that exactly one of the given variables is true
    clauses = []
    n = len(variables)
    if n == 0:
        return clauses
    for i in range(n):
        for j in range(i+1, n):
            clauses.append((-variable(*variables[i]), -variable(*variables[j])))
        clause = [variable(*variables[i]) for i in range(n)]
        clauses.append(clause)
    return clauses



puzzle =      ([[0,0,0,3,2,0,0,0,4],
               [0,8,1,0,0,0,0,0,0],
               [0,0,0,0,0,0,0,0,0],
               [0,0,0,1,0,7,0,5,0],
               [2,0,0,0,0,0,0,0,0],
               [0,0,0,0,0,8,0,0,0],
               [4,2,0,0,6,0,0,0,0],
               [0,0,0,0,0,0,9,1,0],
               [6,0,0,0,0,0,3,0,0]])
cnf = encode_sudoku(puzzle)

print(cnf)

