# Controls for acts_datafit.py: do the two halves alone also beat LCDM? (If yes, the clumping product is not what the data reward.)
src=open('/mnt/project-files/gravity-v7/de/acts_datafit.py').read().split('res={}')[0]
exec(src)
un10=np.array([1-fcoll(z,sig(1e10)) for z in tz])
ctrl={'cumulative SFR alone':cumS/cumS[0],'unclumped (1e10) alone':un10/un10[0],'SFR rate alone':psi(tz)/psi(0)}
tracers.update(ctrl)
L=fit('LCDM',[0.31,0.68,0.0224]).fun
for k in ctrl:
    r=fit(k,[0.31,0.68,0.0224]); x=chi2(r.x,k)[1]
    print(f"{k:24s}: chi2 {r.fun:.2f} (BAO {x[0]:.2f}, SN {x[1]:.2f}, CMB {x[2]:.2f})  dchi2 vs LCDM {r.fun-L:+.2f}  Om {r.x[0]:.4f} h {r.x[1]:.4f}")
