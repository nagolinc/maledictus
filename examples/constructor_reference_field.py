from nagini_contracts.contracts import *


class Child:
    def __init__(self, parent: "Parent") -> None:
        Ensures(Acc(self.parent))
        Ensures(self.parent is parent)
        self.parent: "Parent" = parent


class Parent:
    def __init__(self) -> None:
        Ensures(Acc(self.child))
        Ensures(Acc(self.child.parent))
        Ensures(self.child.parent is self)
        self.child: "Child" = Child(self)


def verify_parent_identity() -> None:
    parent = Parent()
    Assert(parent.child.parent is parent)
