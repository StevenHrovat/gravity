# Coordinator diagnostics after the photon gate failed (not counted; not part of the plan).
cd "$(dirname "$0")/../.."
py -W ignore actnumber.py run u1 1.1 10 48 4104 runs-gpu/diag/d1_new_L10_therm3000.npz --plane 01 --chains 8 --therm 3000 --meas 300 --every 4 --levels 0,3,8,16 > runs-gpu/diag/d1.log 2>&1; echo "d1 rc=$?"
py -W ignore actnumber_old.py run u1 1.1 8 48 4103 runs-gpu/diag/d2_old_L8.npz --plane 01 --chains 8 --therm 300 --meas 300 --every 4 --levels 0,3,8,16 > runs-gpu/diag/d2.log 2>&1; echo "d2 rc=$?"
