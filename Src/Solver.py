"""
CDCL SAT Solver with VSIDS and Fast 2WL

This Class creates a CDCL solver.

Usage:
solver = Solver()
solver.readfile({filename})
solver.solve()
OPTIONAL
solver.checker()

@author: Marco Scully
"""


class Solver:
    def __init__(self):
        self.base_state()


    def checker(self):
        self.assignments = [i if i != 0 else 1 for i in self.assignments]

        for i in self.clauses:
            # Checking if both are positive or if both are negative (-ve*-ve=+ve and +ve*+ve=+ve)
            if not any(map(lambda lit: 1 if lit * self.assignments[abs(lit)] > 0 else 0, i)):
                return False
        return True

    def base_state(self):
        self.clauses = []
        self.assignments = []
        self.num_literals = 0
        self.num_clauses = 0
        self.level = 0
        self.trail = []
        self.reasons = []
        self.assignment_level = []

        self.vsids = []
        self.vsids_inc = 1.0
        self.watch_list = dict()

    def readfile(self, f):
        self.base_state()
        clauses = []
        with open(f) as cnf:
            for line in cnf:
                if line.startswith("c"):
                    continue
                elif line.startswith("p"):
                    self.num_literals = int(line.split()[2])
                    self.vsids = [0.0] * (self.num_literals + 1)
                    break

            for line in cnf:
                s = line.strip()
                if s and not s.startswith("%") and not s.startswith("0"):
                    a = [int(x) for x in s.split() if x != "0"]
                    if a:
                        clauses.append(a)
                        for k in a:
                            self.vsids[abs(k)] += 1.0

        self.clauses = clauses
        self.num_clauses = len(clauses)
        self.reasons = [-1] * (self.num_literals + 1)
        self.assignment_level = [-1] * (self.num_literals + 1)
        self.watch_list = {lit: [] for i in range(1, self.num_literals + 1) for lit in (i, -i)}

        # Setup 2WL: clause[0] and clause[1] are ALWAYS the watched literals
        for index, clause in enumerate(self.clauses):
            if len(clause) >= 2:
                self.watch_list[clause[0]].append(index)
                self.watch_list[clause[1]].append(index)

    def pick_literal(self):
        max_act = -1.0
        best_lit = 0
        for i in range(1, self.num_literals + 1):
            if self.assignments[i] == 0:
                if self.vsids[i] > max_act:
                    max_act = self.vsids[i]
                    best_lit = i
        return best_lit

    def assign(self, literal, reason_clause):
        var = abs(literal)
        self.assignments[var] = 1 if literal > 0 else -1
        self.reasons[var] = reason_clause
        self.assignment_level[var] = self.level
        self.trail.append(literal)

    def backtrack(self, level):
        while self.trail and self.assignment_level[abs(self.trail[-1])] > level:
            var = abs(self.trail.pop())
            self.assignments[var] = 0
            self.assignment_level[var] = -1
            self.reasons[var] = -1
        self.level = level

    # Fast Inlined Unit Propagation
    def unit_propagation(self, start_idx):
        idx = start_idx
        assignments = self.assignments

        while idx < len(self.trail):
            p = self.trail[idx]
            idx += 1
            falsified_lit = -p

            # Fast watch list iteration without copying
            watches = self.watch_list[falsified_lit]
            i = 0
            while i < len(watches):
                clause_idx = watches[i]
                clause = self.clauses[clause_idx]

                # Make sure falsified_lit is at clause[1]
                if clause[0] == falsified_lit:
                    clause[0], clause[1] = clause[1], clause[0]

                # If clause[0] (other watch) is satisfied -> skip
                other_watch = clause[0]
                other_val = assignments[abs(other_watch)]
                if (other_watch > 0 and other_val == 1) or (other_watch < 0 and other_val == -1):
                    i += 1
                    continue

                # Look for a replacement watch
                found_new = False
                for k in range(2, len(clause)):
                    lit = clause[k]
                    val = assignments[abs(lit)]
                    # If lit is not falsified:
                    if not ((lit > 0 and val == -1) or (lit < 0 and val == 1)):
                        clause[1], clause[k] = clause[k], clause[1]
                        self.watch_list[lit].append(clause_idx)

                        # Remove clause_idx from current watch list in-place fast
                        watches[i] = watches[-1]
                        watches.pop()
                        found_new = True
                        break

                if not found_new:
                    # Unit or Conflict
                    if other_val == 0:
                        self.assign(other_watch, clause_idx)
                        i += 1
                    else:
                        return clause_idx

        return None

    def resolve_conflict(self, clause_index):
        current_clause = set(self.clauses[clause_index])

        # VSIDS Activity Bump
        for lit in current_clause:
            self.vsids[abs(lit)] += self.vsids_inc

        curr_level_count = sum(1 for lit in current_clause if self.assignment_level[abs(lit)] == self.level)

        for lit in reversed(self.trail):
            if curr_level_count <= 1:
                break

            var = abs(lit)
            if var in current_clause or -var in current_clause:
                reason_idx = self.reasons[var]
                if reason_idx is not None and reason_idx != -1:
                    reason_clause = self.clauses[reason_idx]

                    for r_lit in reason_clause:
                        self.vsids[abs(r_lit)] += self.vsids_inc

                    # Resolve out variable
                    current_clause.discard(var)
                    current_clause.discard(-var)
                    for r_lit in reason_clause:
                        if abs(r_lit) != var:
                            current_clause.add(r_lit)

                    curr_level_count = sum(1 for l in current_clause if self.assignment_level[abs(l)] == self.level)

        # Rescale VSIDS increment instead of entire array
        self.vsids_inc *= 1.05
        if self.vsids_inc > 1e100:
            for v in range(1, self.num_literals + 1):
                self.vsids[v] *= 1e-100
            self.vsids_inc *= 1e-100

        # Find 1-UIP
        uip_lit = next(l for l in current_clause if self.assignment_level[abs(l)] == self.level)

        # Calculate backtrack level
        levels = [self.assignment_level[abs(l)] for l in current_clause if self.assignment_level[abs(l)] != self.level]
        backtrack_level = max(levels) if levels else 0

        return list(current_clause), backtrack_level, uip_lit

    def add_clause(self, clause):
        clause_idx = len(self.clauses)
        self.clauses.append(clause)
        self.num_clauses += 1

        # adds to clause to correct literals watch list
        if len(clause) >= 2:
            self.watch_list[clause[0]].append(clause_idx)
            self.watch_list[clause[1]].append(clause_idx)
        elif len(clause) == 1:
            self.watch_list[clause[0]].append(clause_idx)

    def solve(self):
        self.assignments = [0] * (self.num_literals + 1)
        self.level = 0

        if self.unit_propagation(0) is not None:
            return "UNSAT"

        while True:
            decision = self.pick_literal()
            if decision == 0:
                return "SAT"

            self.level += 1
            start_idx = len(self.trail)
            self.assign(decision, None)

            conflict = self.unit_propagation(start_idx)

            while conflict is not None:
                if self.level == 0:
                    return "UNSAT"

                resolved_clause, backtrack_level, uip_lit = self.resolve_conflict(conflict)
                self.backtrack(backtrack_level)
                self.add_clause(resolved_clause)

                start_idx = len(self.trail)
                self.assign(uip_lit, len(self.clauses) - 1)

                conflict = self.unit_propagation(start_idx)
