from collections import namedtuple
import functools as ft
import operator

"""Turns a function into a generator, even if there is no yield statement in its body."""
def generator(f):
	@ft.wraps(f)
	def wrapper(*args, **kwargs):
		yield from ()
		return f(*args, **kwargs)

	return wrapper

"""A simple testing framework."""
def test(pred, arg):
	arg_val = eval(arg)
	if not eval('lambda arg: ' + pred)(arg_val):
		print(f"Test failed:\n  pred := {pred}\n  arg := {arg}\n  eval(arg) := {arg_val}")

"""Used to get around the expression-statement distinction."""
def seq(fs, *args, **kwargs):
	for f in fs[:-1]:
		f(*args, **kwargs)

	return fs[-1](*args, **kwargs)

class shiftable_iterator:
	def __init__(self, iterator):
		self.iterator = iterator
		self.stack = []

	def __iter__(self):
		return self

	def __next__(self):
		try:
			return self.stack.pop()
		except IndexError:
			return next(self.iterator)	

	def shift(self, val):
		self.stack.append(val)

	def peek(self):
		val = next(self)
		self.shift(val)
		return val

def iter_shiftable(obj):
	return shiftable_iterator(iter(obj))

test("arg == 0", "seq((operator.methodcaller('shift', 0), next), iter_shiftable((1, 2, 3)))")
test("arg == 1", "seq((operator.methodcaller('shift', 0), next, next), iter_shiftable((1, 2, 3)))")

class Index(namedtuple('Index', 'val')):
	def __str__(self):
		return f"index {self.val}"

def with_indices(s):
	return map(lambda p: (Index(p[0]), p[1]), enumerate(s))
 
Token = namedtuple('Token', 'js val')

def scan(s):
	"""Scan a string of Kernel source code and yield the resulting tokens.

	The parameter `s` is expected to be an iterator over 2-tuples, where each first element is a
	character and each second element is location info for the corresponding character. However,
	if it's just an iterator over characters, each character will be equipped with its index within
	the string as its location info by default.

	"Location info" can be any object; the object will be stored against resulting tokens, and if
	an error is encountered during parsing, the error message will include the str of the
	object."""

	s = iter_shiftable(s)

	try:
		first_char = s.peek()

		if isinstance(first_char, str):
			s = iter_shiftable(with_indices(s))
	except StopIteration:
		pass

	def scan_whitespace():
		for i, c in s:
			if c == ';':
				return scan_comment
			elif c == '"':
				
			elif c in ('(', ')'):
				yield Token((i,), c)
			elif not c.isspace():
				s.shift((i, c))
				return scan_symbol

	@generator
	def scan_comment():
		for i, c in s:
			if c == '\n':
				s.shift((i, c))
				return scan_whitespace

	def scan_symbol():
		items = []

		def yield_token():
			js, cs = zip(*items)
			yield Token(js, ''.join(cs))

		for i, c in s:
			if c.isspace() or c in (';', '(', ')'):
				yield from yield_token()
				s.shift((i, c))
				return scan_whitespace
			else:
				items.append((i, c))

		yield from yield_token()

	scanner = scan_whitespace

	while scanner is not None:
		scanner = yield from scanner()

test("arg == ()", "tuple(scan(''))")
test("arg == (Token((Index(0),), 'x'),)", "tuple(scan('x'))")
test("arg == (Token((Index(0),), '('), Token((Index(1),), 'x'), Token((Index(2),), ')'))", "tuple(scan('(x)'))")
test("arg == (Token((Index(0),), '('), Token((Index(1), Index(2)), 'xy'), Token((Index(3),), ')'))", "tuple(scan('(xy)'))")
test("arg == (Token((Index(0),), '('), Token((Index(1),), 'x'), Token((Index(3),), 'y'), Token((Index(4),), ')'))", "tuple(scan('(x y)'))")
test("arg == (Token((Index(0),), '('), Token((Index(1),), 'x'))", "tuple(scan('(x;y)'))")

class KernelSyntaxError(Exception):
	def __init__(self, message, js):
		super().__init__(message)
		self.js = js

def parse(toks):
	stack = [[]]

	for js, tok in toks:
		if tok == '(':
			stack.append([])
		elif tok == ')':
			ls = stack.pop()
			stack[-1].append(KernelList(ls))
		else:
			stack[-1].append(tok)

	ls = stack.pop()
	return KernelList(ls)
