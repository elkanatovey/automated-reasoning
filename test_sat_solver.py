"""Tests all operator tasks."""

from propositions.syntax_test import *
from propositions.semantics_test import *
from propositions.operators_test import *

def test_preprocess(debug=False):
    test_to_NNF_push_negations(debug=False)
    test_to_NNF_eliminate_IFF_and_IF(debug=False)
    test_to_NNF(debug=False)
    test_to_NNF_to_CNF(debug=False)
    test_to_tseitin_step1(debug=False)
    test_to_tseitin_step2_short(debug=False)
    test_to_tseitin_short(debug=False)
    test_preprocess_clauses_short(debug=True)

test_preprocess(True)

