"""Pytest configuration for the automated-reasoning test suite.

Forces a non-interactive matplotlib backend before any test module imports
``matplotlib.pyplot`` so that the visualization tests (which call
``plt.show()``) never open a GUI window or block in a headless environment.
"""

import matplotlib

matplotlib.use("Agg")
