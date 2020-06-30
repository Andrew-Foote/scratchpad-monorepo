import hypothesis as hyp
from hypothesis import strategies as st
from main import Var, Term, parse

vars_ = st.builds(Var, st.integers(0))
terms = st.recursive(
		st.builds(Term.VAR, vars_),
		lambda terms: st.one_of(
			st.builds(Term.ABST, vars_, terms),
			st.builds(Term.APP, terms, terms)
		)
)

def test_var_str():
	assert str(Var(0)) == 'a'
	assert str(Var(1)) == 'b'
	assert str(Var(25)) == 'z'
	assert str(Var(26)) == 'a1'
	assert str(Var(52)) == 'a2'

def test_term_str():
	assert str(Term.VAR(Var(0))) == 'a'
	assert str(Term.ABST(Var(0), Term.VAR(Var(1)))) == 'λa.b'
	assert str(Term.APP(Term.VAR(Var(0)), Term.VAR(Var(1)))) == 'ab'
	assert str(Term.APP(Term.APP(Term.VAR(Var(0)), Term.VAR(Var(1))), Term.VAR(Var(2)))) == 'abc'
	assert str(Term.APP(Term.VAR(Var(0)), Term.APP(Term.VAR(Var(1)), Term.VAR(Var(2))))) == 'a(bc)'
	assert str(Term.ABST(Var(0), Term.APP(Term.VAR(Var(1)), Term.VAR(Var(2))))) == 'λa.bc'
	assert str(Term.APP(Term.ABST(Var(0), Term.VAR(Var(1))), Term.VAR(Var(2)))) == '(λa.b)c'
	assert str(Term.APP(Term.VAR(Var(0)), Term.ABST(Var(1), Term.VAR(Var(2))))) == 'a(λb.c)'

@hyp.given(terms)
def test_term_str(term):
	str(term)

def test_free_vars():
	assert Term.VAR(Var(0)).free_vars() == {Var(0)}
	assert Term.ABST(Var(0), Term.VAR(Var(0))).free_vars() == set()
	assert Term.ABST(Var(0), Term.VAR(Var(1))).free_vars() == {Var(1)}
	assert Term.APP(Term.VAR(Var(0)), Term.VAR(Var(0))).free_vars() == {Var(0)} 
	assert Term.APP(Term.VAR(Var(0)), Term.VAR(Var(1))).free_vars() == {Var(0), Var(1)}

@hyp.given(terms, vars_)
def test_has_free(term, var):
	term.has_free(var)

@hyp.given(terms, vars_, terms)
def test_has_substitutable(term, var, repl):
	term.has_substitutable(var, repl)