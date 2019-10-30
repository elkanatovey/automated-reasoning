# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: logic_utils.py

"""Python infrastructure for our logic course."""

from functools import wraps
from typing import Any, Dict, Iterator, Set, Type, TypeVar

T = TypeVar('T')

def frozen(cls: Type[T]) -> Type[T]:
    """A class decorator that disallows assignment to instance variables after
    construction."""
    original_init = cls.__init__
    original_setattr = cls.__setattr__
    original_delattr = cls.__delattr__
    mutable_ids: Set[int] = set()
    @wraps(cls.__setattr__)
    def setattr_wrapper(self, name, value):
        if id(self) in mutable_ids:
            original_setattr(self, name, value)
        else:
            raise Exception("Cannot assign to field '" + name +
                            "' of immutable class '" + cls.__name__ + "'")
    @wraps(cls.__delattr__)
    def delattr_wrapper(self, name, value):
        if id(self) in mutable_ids:
            original_delattr(self, name, value)
        else:
            raise Exception("Cannot delete field '" + name +
                            "' of immutable class '" + cls.__name__ + "'")
    @wraps(cls.__init__)
    def init_wrapper(self, *args, **kwargs):
        mutable_ids.add(id(self))
        original_init(self, *args, **kwargs)
        mutable_ids.remove(id(self))

    setattr(cls, '__setattr__', setattr_wrapper)
    setattr(cls, '__delattr__',  delattr_wrapper)
    setattr(cls, '__init__', init_wrapper)
    return cls

class frozendict(Dict[Any, Any]):
    """An immutable variant of the built-in dict class."""

    def __init__(self, *args, **kwargs):
        super().update(dict(*args, **kwargs))
        
    def update(self, *args, **kwargs):
        raise Exception('Cannot modify a frozendict')

    __delattr__ = __delitem__ = __setattr__ = __setitem__ = clear = pop = \
                  popitem = setdefault = update

class __prefix_with_index_sequence_generator:
    """ A generator for a sequence of the form 'z1', 'z2', 'z3', ..., where the
    prefix 'z' is customizable. """

    def __init__(self, prefix: str) -> None:
        self.__prefix = prefix
        self.__counter = 0

    def __iter__(self) -> Iterator[str]:
        return self

    def __next__(self) -> str:
        self.__counter = self.__counter + 1
        return self.__prefix + str(self.__counter)

    def _reset_for_test(self) -> None:
        """ Reset this generator. For use by tests only """
        self.__counter = 0

# A generator for fresh variables names. The first call to: 
# next(fresh_variable_name_generator)
# will return 'z1', the second call to:
# next(fresh_variable_name_generator)
# will return 'z2', and so on. """
fresh_variable_name_generator: Iterator[str] = \
    __prefix_with_index_sequence_generator('z')

# A generator for fresh constant names. The first call to: 
# next(fresh_constant_name_generator)
# will return 'c1', the second call to:
# next(fresh_constant_name_generator)
# will return 'c2', and so on. """
fresh_constant_name_generator: Iterator[str] = \
    __prefix_with_index_sequence_generator('c')
