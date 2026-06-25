from typing import Callable, TypeVar

P = TypeVar('P')
Q = TypeVar('Q')
R = TypeVar('R')

def chain(
    hPQ: Callable[[P], Q],
    hQR: Callable[[Q], R],
    hP: P
) -> R:
    return hQR(hPQ(hP))


# Concrete functions to pass through
def double(x: int) -> int:
    return x * 2

def to_string(x: int) -> str:
    return str(x)


# This should type-check: int -> int -> str, starting with int
result: str = chain(double, to_string, 5)
print(result)


# This should FAIL type checking
bad_result = chain(double, to_string, "hello")

def needs_float(x: float) -> str:
    return f"{x:.2f}"

worse_result = chain(double, needs_float, 5)
print(worse_result)