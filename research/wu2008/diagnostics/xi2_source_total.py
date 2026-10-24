"""Plan the remaining source-count payments; floating diagnostics, never proof.

Input: JSON output from classical_coefficient.py. The four-window subtotal
matches SourceContinuousCount using the candidate alone (not its maximum with
W17). The seven-window projection additionally assumes the three coupled
publication gains can be transferred to actual counts; that step is unproved.
The small positive HighConsumer.highGain is omitted throughout.
"""
import argparse
import json
from math import log
from xi2_count_gain import ALPHA, CANDIDATE, gain
from xi2_source_gain import source_gains


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('classical_json')
    args = parser.parse_args()
    with open(args.classical_json) as stream:
        classical = json.load(stream)['runs'][-1][
            'classical_coefficient_without_any_H_h_Psi_gain']
    publication = [15247971, 13898757, 11776059, 9405211,
                   6558950, 3536751, 1056651]
    windows = []
    for j, numerator in enumerate(publication):
        a = 1/(6*ALPHA) if j == 0 else 2+(2+j)/10
        b = 2+(3+j)/10
        windows.append(8*log(b*(1-2*ALPHA*a)/(a*(1-2*ALPHA*b)))*numerator/1e9)
    runs = []
    for tolerance in [1e-8, 1e-10]:
        sources = source_gains(CANDIDATE, tolerance)
        sixth = gain(CANDIDATE, tolerance)
        four = classical+(sources['single_source_gain']+sources['fifth_grid_gain']+
                          sixth+sum(windows[3:]))/4
        projection = four+sum(windows[:3])/4
        runs.append({'tolerance': tolerance, 'classical_coefficient': classical,
                     'single_gain': sources['single_source_gain'],
                     'fifth_gain': sources['fifth_grid_gain'], 'sixth_gain': sixth,
                     'four_window_gain': sum(windows[3:]),
                     'unproved_three_window_gain': sum(windows[:3]),
                     'four_window_subtotal': four,
                     'seven_window_projection': projection,
                     'projected_margin_over_4491_over_5000': projection-4491/5000})
    print(json.dumps({'kind': 'floating_diagnostic_not_a_Lean_certificate',
                      'classical_input': args.classical_json, 'runs': runs}, indent=2))


if __name__ == '__main__':
    main()
