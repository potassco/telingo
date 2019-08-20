"""
This module contains simple helper functions.
"""

def getattr_(obj, *attrs):
    """
    Returns the first attribute of the given object that is available.
    """
    for attr in attrs:
        if hasattr(obj, attr):
            return getattr(obj, attr)
    raise AttributeError(
        '{} does not have any of the attributes {}'.format(
            obj.__class__.name,
            ','.join(('"{}"'.format(attr) for attr in attrs))))
