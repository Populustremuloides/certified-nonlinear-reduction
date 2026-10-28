# Computational method and scope

The physical reference is the 96-state switch reconstruction in `physics.py`.
Its time coordinate is measured in units of 10 microseconds. Voltage enters as
its square. The simulator stops at gap-domain exit instead of clipping states.
Positive and negative voltage pulses therefore share a physical reference.

The coordinate chart retains every physical coordinate. Its scale and the
additional observable regression use training data only. The eight-observable
lifting is state inclusive and origin preserving. During prediction every lifted
coordinate evolves freely; the encoder is not reevaluated at every step.

Two autonomous coefficient networks share the same injection K. Their normalized
average has norm bounded by the reconstructed state norm, with injection 2K.
Two actuation reservoirs have combined driver norm sqrt(2) times the applied
input magnitude. The associated control injection is sqrt(2)[P0 P1]. The nominal
physical-input matrix is exactly zero. The directed-rounding checker encloses
the real sqrt(2) factor and checks the actual stored reduced blocks.

Fresh initialization fits the autonomous observable matrix on post-release
training samples. A declared ridge-strength grid seeks a Schur regression;
no artificial latent poles are inserted. A common autonomous-port scale is
chosen for feasibility. A common head-scale search requires finite training
and development rollouts in both arms. These searches are logged and do not inspect reserved
cases or select an instability event.

The two arms start with identical coefficients and differ in normalization.
Warm-up uses windows initialized from physical training states. Full fitting
then differentiates through uninterrupted zero-initialized full and reduced
training trajectories. Activation checkpointing recomputes intermediate states
without truncating state gradients. Alternating matrix regression is accepted
only when it improves the full objective and passes the declared matrix checks.
Neural full-phase line searches also reject nonfinite development rollouts.
Warm-up blocks with nonfinite development rollouts are rolled back and their
step size is reduced; every rejection is recorded.
Only the normalized architecture turns those checks into nonlinear certificates.

Selection minimizes development prediction loss. The models are frozen before
reserved physical references are generated. The illustrated training pulse is
5.5 V for 100 microseconds; independent reserved cases are reported separately.
Error uses all 96 scaled physical coordinates. A numerical growth stop supplies
a finite observed-prefix error lower bound, not an invented infinite error.

The default full-phase plateau criterion is less than 0.5 percent improvement
in each primary/full/reduced prediction loss across three validation intervals,
after at least 64 full updates. A curvature reset and alternating 0.3x/3x
step scales must also fail to restore improvement. The configured update ceiling
is a resource limit; it is not called convergence. The best development
checkpoint is retained even when the final update is worse.
