"""Independent finite floating-point checks. The mathematical result uses real arithmetic."""
import math
from itertools import product
def s(x):
    return x/(1+math.exp(-x))
if __name__=="__main__":
    for x,p,q,u in product(range(-8,9),range(-2,3),range(-2,3),range(-2,3)):
        lhs=p*u*s(x)-q*u*s(-x)
        rhs=p*u*x+(p-q)*u*s(-x)
        assert math.isclose(lhs,rhs,abs_tol=1e-13)
    assert abs(s(-1))>0.2
    print("2125 route and input combinations checked")
