import numpy.linalg as lin
import numpy as np
import json
import sys
import os

if __name__ == "__main__":
    N = M = 0
    if len(sys.argv) == 2:
        N = int(sys.argv[1])
        M = N
    elif len(sys.argv) == 3:
        N = int(sys.argv[1])
        M = int(sys.argv[2])
    else:
        print(
            """Incorrect usage-
                For square N X N matrix: python3 input-creator N
                For rectangular N X M matrix: python3 input-creator N M"""
        )
        exit(1)

    MAX_ELEM = 10
    mat_ran = np.random.uniform(-MAX_ELEM, MAX_ELEM, size=(N, M))
    # Inf norm
    norm = np.linalg.norm(mat_ran, ord=2)
    # rescale matrix so that ||mat||_inf \in (1,100)
    mat_ran = mat_ran / norm * np.random.uniform(1, 100)

    U, D, V = lin.svd(mat_ran)
    mat_ran = mat_ran.tolist()
    U = U.tolist()
    V = V.tolist()
    D = D.tolist()

    dict_svd = {"m": mat_ran, "u": U, "d": D, "v": V}

    json_file_path = "./data/matrix.in"
    if not os.path.exists("./data"):
        os.makedirs("./data")

    with open(json_file_path, "w") as json_file:
        # Write the dictionary to the JSON file
        json.dump(dict_svd, json_file, indent=4)

    # change m to be wrong
    rand_i = np.random.randint(N)
    rand_j = np.random.randint(M)
    mat_ran[rand_i][rand_j] += 1e-7
    dict_svd = {"m": mat_ran, "u": U, "d": D, "v": V}

    json_file_path = "./data/matrix-wrong.in"

    with open(json_file_path, "w") as json_file:
        # Write the dictionary to the JSON file
        json.dump(dict_svd, json_file, indent=4)

    print(f"Python: Successfully created inputs for {N} X {M}!")
