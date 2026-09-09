import json
import unittest
from run_extract import check_module_receipts
from run_coverage import parse_results, identifier


class RunnerTests(unittest.TestCase):
    def test_module_receipts(self):
        raw = b'{"module":"M"}\n'
        check_module_receipts(raw, 'module=M declarations=1 parts=1\nmodule=Empty declarations=0 parts=1\n', ['M','Empty'])
        for text in ['', 'module=M declarations=2 parts=1\n', 'module=M declarations=1 parts=1\nmodule=M declarations=1 parts=1\n']:
            with self.assertRaises(ValueError): check_module_receipts(raw,text,['M'])

    def test_coverage_inventory(self):
        row={'target':'A','provider':'B','status':'not_covered'}
        text='PROOFOPT_COVERAGE '+json.dumps(row)
        self.assertEqual(parse_results(text,[('A','B')]),[row])
        for bad in ['',text+'\n'+text]:
            with self.assertRaises(ValueError): parse_results(bad,[('A','B')])

    def test_false_success_receipt(self):
        text='PROOFOPT_COVERAGE '+json.dumps({'target':'A','provider':'B','status':'success'})
        with self.assertRaises(ValueError):parse_results(text,[('A','B')])

    def test_command_injection_rejected(self):
        for value in ['A\naxiom x : False','A B','A/-comment-/','', 'A.«bad»']:
            with self.assertRaises(ValueError):identifier(value)
        self.assertEqual(identifier('MathlibNt.α₁_prime\''), 'MathlibNt.α₁_prime\'')


if __name__=='__main__':unittest.main()
