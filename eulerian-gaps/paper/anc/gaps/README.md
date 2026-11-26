# Verifying the Eulerian-gap section

Use Python 3.12 or later, with assertions enabled. All arithmetic checks use the standard library. From this directory run:

    python3 -B two_radii.py
    python3 -B short_signed.py
    python3 -B central-budgets.py
    python3 -B verify_brackets.py

The first two scripts evaluate finite coefficient-majorant heads with an analytic bound for the remaining positive tail. The third checks the four defect ranges in the central-root argument. The last reconstructs the restricted alphabet polynomials in both directions, transforms them to genuine descent rows, builds the enclosing Eulerian polynomial by its elementary recurrence and checks every rational sign from ranks 6 through 127. It reads the checked-in brackets and performs no floating-point root isolation. The neighboring files under anc reproduce the two results of the first version.
