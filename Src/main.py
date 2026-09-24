from time import perf_counter
from Solver import Solver


start = perf_counter()
solver = Solver()
for i in range(1, 1001):
    print(f"Number: {i}")
    solver.readfile(f"../Benchmarks/uf100-430/uf100-0{i}.cnf")
    solver.solve()
    #print(solver.checker())

end = perf_counter()
print(end - start)
