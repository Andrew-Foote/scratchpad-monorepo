import functools as ft
import hypothesis as hyp
from hypothesis import strategies as st
import main as m

term_vars = st.builds(m.TermVar, name=st.text())

# a cap on the arity is needed to avoid memory issues
fun_symbols = st.builds(m.FunSymbol, name=st.text(), arity=st.integers(min_value=0, max_value=10))
rel_symbols = st.builds(m.RelSymbol, name=st.text(), arity=st.integers(min_value=0, max_value=10))
connectives = st.builds(m.Connective, name=st.text(), arity=st.integers(min_value=0, max_value=10))

quantifiers = st.builds(m.Quantifier, name=st.text())

terms = st.recursive(
	term_vars,
	lambda terms: fun_symbols.flatmap(
		lambda symbol: st.builds(
			ft.partial(m.FunApp, symbol),
			st.tuples(*((terms,) * symbol.arity))
		)
	)
)

atomic_formulas = rel_symbols.flatmap(
	lambda symbol: st.builds(
		ft.partial(m.RelApp, symbol),
		st.tuples(*((terms,) * symbol.arity))
	)
)

formulas = st.recursive(
	atomic_formulas,
	lambda formulas: st.one_of(
		connectives.flatmap(
			lambda symbol: st.builds(
				ft.partial(m.Connective, symbol),
				st.tuples(*((formulas,) * symbol.arity))
			)
		),
		st.builds(m.Quantify, quantifiers, term_vars, formulas)
	)
)

# Tests that for every term t, every variable x and every formula φ in which x is not free, we have
# φ[t/x] = φ.

@hyp.given(arg=terms, param=term_vars, expr=formulas)
def test_invariance_under_subst_for_bound_var(arg, param, expr):
	hyp.assume(not m.is_free(param, expr))
	assert m.subst(arg, param, expr) == expr

# @hyp.given(st.integers(0).flatmap(lambda n: st.lists(st.integers(), min_size=n, max_size=n)))
# def test_example(arg):
# 	assert arg == list(reversed(arg))

# @st.composite
# def newstrat(draw):
# 	n = draw(st.integers(min_value=0))
# 	return draw(st.lists(st.integers(), min_size=n, max_size=n))

# @hyp.given(st.integers(min_value=0).flatmap(
# 	lambda n: st.lists(st.integers(), min_size=n, max_size=n)
# ))
# @hyp.given(newstrat())
# def test_example2(x):
# 	assert x == x