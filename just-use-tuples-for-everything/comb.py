from contextlib import contextmanager

# can we get around the expression-statement dichotomy by using with for everything?

class NoMatch(Exception): pass

@contextmanager
def match():
	try: yield
	except (ValueError, TypeError, NoMatch): pass

def match_if(cond):
	if not cond: raise NoMatch

def is_var(obj):
	with match():
		sort, name = obj
		match_if(sort == 'var' and isinstance(name, str))

	return False

K = ('constant', 'K')
S = ('constant', 'S')

def is_term(obj):
	with match():
		match_if(is_var(obj))

	with match():
		match_if(obj in (K, S))

		sort, name = obj
		match_if(sort == 'var' and isinstance(name, str))

	with match():
		sort, fun, arg = data
		match_if(sort == 'application' and is_term(fun) and is_term(arg))

	return False

def reducts(term):
	assert is_term(term)
	result = {}

	with match():
		sort, fun, arg = term
		match_if(sort == 'application')
		result.update(map(lambda reduct: ('application', reduct, arg), reducts(fun)))
		result.update(map(lambda reduct: ('application', fun, reduct), reducts(arg)))

		with match():
			sort2, fun2, arg2 = fun
			match_if(sort2 == 'application' and fun2 == K)
			result.add(arg1)

		with match():
			sort2, (sort3, fun2, arg3), arg2 = fun
			match_if(sort2 == sort3 == 'application' and fun2 == S)
			result.add(('application', ('application', arg3, arg), ('application', arg2, arg)))

	return result

def abstract(var, term):
	assert is_var(var)