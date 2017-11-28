#!/usr/bin/env python -W ignore::DeprecationWarning
# -*- coding: utf-8 -*-qq


import re
from sets import Set
from aima import logic

def remove_double_bracket(a):
	res = re.sub("{{", "{", a)
	res = re.sub("}}", "}", res)

	return res

def rewrite_implication(formula):
	if "->" in formula:
		formula = re.sub("->", ">>", formula)
		formula = re.sub("<>>", "<=>", formula)

	return formula

def subformula(formula):
	sf = set()
	formulas = []
	formula = rewrite_implication(formula)
	
	
	if (">>" in formula) or ("<=>" in formula):
		formula = logic.expr(formula)
		formula = logic.eliminate_implications(formula)

	
	formula = logic.expr(formula)
	sf.update(set([formula]))
	formulas.append(formula)
	
	while True:
		n = len(formulas)
		
		for f in formulas:
			f = logic.literal_symbol(f)
			sf.update(set([f]))

			con = logic.conjuncts(f)
			sf.update(set(con))

			dis = logic.disjuncts(f)
			sf.update(set(dis))

		for f in sf:
			if f not in formulas:
				formulas.append(f)

		if n == len(formulas):
			return formulas



def cnf(formula):
	result = "{"
	formula = str(formula)

	formula = rewrite_implication(formula)
	
	formula = logic.to_cnf(logic.expr(formula))
	clauses = logic.conjuncts(formula)

	clauses = set(clauses)
	clauses = list(clauses)
	
	for c in clauses:
		if logic.tt_true(c):
			clauses.remove(c)

	for c in clauses:
		if logic.tt_true(c) is False:
			result = result + "{" 
			lits = logic.disjuncts(c)

			lits = set(lits)
			lits = list(lits)

			for s in lits:
				if lits.index(s) == len(lits) - 1:
					result = result + str(s) + "}"
				else:
					result = result + str(s) + ", "

			if clauses.index(c) != len(clauses) - 1:
				result = result + ","

	result = result + "}"

	return result


def res(formula):
	formula = rewrite_implication(formula)
	
	formula = logic.to_cnf(logic.expr(formula))
	clauses = logic.conjuncts(formula)

	print "CNF: " + cnf(formula)
	m = 1
	for c in clauses:
		if logic.tt_true(c):
			clauses.remove(c)
		else:
			a = remove_double_bracket(cnf(c))
			print str(m) + ": " + a
			m += 1
	
	new = set()

	while True:
		n = len(clauses)
		pairs = [(clauses[i], clauses[j]) for i in range(n) for j in range(i+1, n)]

		for (ci, cj) in pairs:
			resolvents = logic.pl_resolve(ci, cj)

			if (len(resolvents) != 0):
				if (resolvents[0] not in new):
					if (resolvents[0] is logic.FALSE):
						print str(m) + ": {}"
					else:
						print str(m) + ": " + remove_double_bracket(cnf(resolvents[0])) + " --- (" + str(clauses.index(ci)+1) + ", " + str(clauses.index(cj)+1) + ")"
						m += 1

			if logic.FALSE in resolvents:
				return True
			
			
			new.update(set(resolvents))

		if new.issubset(clauses):
			return False

		for c in new:
			if c not in clauses:
				clauses.append(c)


def main():
	operator = ["|", "&", "~", "->", "<->", ")", "("]
	num_formula = int(raw_input())
	cmds = []

	for i in xrange(0, num_formula):
		inp = raw_input()
		cmds.append(inp)
	

	for f in cmds:
		x = f.split(" ")

		cmd = x[0]
		formula = inp[len(cmd)+1:]
		
		if cmd == "ecnf":
			print f
			print cnf(formula)
		
		elif cmd == "res":
			a = res(formula)

			if a is True:
				print "unsatisfiable"
			else:
				print "satisfiable"

		elif cmd == "valid":
			print "check if ~" + formula + " is unsatisfiable"
			formula = "~" + formula
			a = res(formula)

			if a is True:
				print "unsatisfiable"
				print formula + " is valid"
			else:
				print "satisfiable"
				print formula + " is not valid"
		
		elif cmd == "ent":
			opt = re.sub("\) \(", ") ? (", formula)
			formula = re.sub("\) \(", ") & ~(", formula)

			formula = "(" + formula + ")"

			print "check if " + formula + " is unsatisfiable"
			a = res(formula)

			if a is True:
				print "unsatisfiable"
				x = opt.split("?")
				print x[0] + "entails" + x[1]
			else:
				print "satisfiable"
				x = opt.split("?")
				print x[0] + "does not entails" + x[1]

		elif cmd == "sub":
			sf = subformula(formula)

			for f in sf:
				print f

			print formula + " has " + str(len(sf)) + " different formula"



if __name__ == '__main__':
	main()