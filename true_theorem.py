from typing import TypeVar

P = TypeVar('P')

def identity(hP: P) -> P:
    return hP