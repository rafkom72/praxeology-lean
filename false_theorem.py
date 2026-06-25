from typing import TypeVar

P = TypeVar('P')
Q = TypeVar('Q')

# Claim: P implies Q (for any P, Q). This is FALSE in general.
def bogus(hP: P) -> Q:
    return hP