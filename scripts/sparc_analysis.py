#!/usr/bin/env python3

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
import os
import pandas as pd

# Sample SPARC data loader (in real use, download from http://astroweb.cwru.edu/SPARC/)
def load_sparc_data():
    # For demo, synthetic data for one galaxy
    # Real implementation would load CSV with r, v_obs, v_err for 175 galaxies
    r = np.linspace(1, 20, 20)  # kpc
    v_obs = 150 * np.ones_like(r)  # flat curve, km/s
    v_err = 5 * np.ones_like(r)
    return {'demo_galaxy': (r, v_obs, v_err)}

# Recognition weight model for velocity
 def model_velocity(r, M, a0=1.2e-10):
    G = 4.3e-6  # pc/Msun (km/s)^2
    v_newton = np.sqrt(G * M / r)
    v_mond = np.sqrt(v_newton**2 + np.sqrt(G * M * a0))
    return v_mond  # Simplified MOND-like from bandwidth

# Fit function for chi2
 def fit_galaxy(r, v_obs, v_err, gal_name):
    popt, _ = curve_fit(lambda r, M: model_velocity(r, M), r, v_obs, sigma=v_err, p0=[1e11])
    v_fit = model_velocity(r, *popt)
    chi2 = np.sum(((v_obs - v_fit) / v_err)**2)
    return chi2 / len(r), popt[0]

# Main analysis
 def main():
    data = load_sparc_data()
    chi2s = []
    for gal, (r, v_obs, v_err) in data.items():
        chi2_n, M_fit = fit_galaxy(r, v_obs, v_err, gal)
        chi2s.append(chi2_n)
        print(f'Galaxy {gal}: χ²/N = {chi2_n:.2f}, M = {M_fit:.2e} Msun')
    avg_chi2 = np.mean(chi2s)
    print(f'Average χ²/N for {len(data)} galaxies: {avg_chi2:.2f}')
    # Plot example
    plt.errorbar(r, v_obs, yerr=v_err, fmt='o', label='Observed')
    plt.plot(r, model_velocity(r, M_fit), label='Fit')
    plt.xlabel('Radius (kpc)'); plt.ylabel('Velocity (km/s)')
    plt.legend(); plt.title('Demo Galaxy Rotation Curve')
    plt.savefig('Scripts/demo_fit.png')

if __name__ == '__main__':
    main() 