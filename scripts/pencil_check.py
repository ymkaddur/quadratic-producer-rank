"""Coordinate checks of the binary-plane discriminant and the two output identities."""
from itertools import product


def main():
    outputs=0
    for x,y in product(range(-5,6),repeat=2):
        s,t,u=x*x,y*y,(x+y)**2
        assert (s-t,u-s-t)==(x*x-y*y,2*x*y)==((x-y)*(x+y),2*x*y)
        outputs+=1
    for a,b in product(range(-5,6),repeat=2):
        determinant=a*(-a)-b*b
        assert (determinant==0)==(a==b==0)
    print(outputs,"integer inputs checked; the unrestricted real lower bound is in BinaryPencil.lean")


if __name__=="__main__":
    main()
