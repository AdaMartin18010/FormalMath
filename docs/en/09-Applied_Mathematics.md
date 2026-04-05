---
title: Applied Mathematics (应用数学)
msc_primary: 00A99
processed_at: '2026-04-05'
---
# Applied Mathematics (应用数学)

This document provides bilingual (English-Chinese) definitions, notations, and examples for 20 core concepts in applied mathematics.

---

## 1. Numerical Analysis (数值分析)

**MSC Code:** 65-XX

### English Definition
Numerical analysis designs algorithms for solving mathematical problems approximately, with attention to accuracy, stability, and efficiency. It bridges continuous mathematics with discrete computation.

### 中文定义
数值分析设计算法近似求解数学问题，关注精度、稳定性和效率。它连接连续数学与离散计算。

### Notation
- Floating-point arithmetic
- Condition number: $\kappa(A) = \|A\| \|A^{-1}\|$
- Truncation error vs roundoff error
- Convergence rate: linear, quadratic, etc.

### Example
- Solving $Ax = b$
- Eigenvalue computation
- Interpolation and approximation

---

## 2. Finite Difference Method (有限差分法)

**MSC Code:** 65M06, 65N06

### English Definition
The finite difference method approximates derivatives by differences on a grid. It discretizes differential equations to algebraic systems. Stability and convergence depend on step sizes.

### 中文定义
有限差分法在网格上用差分近似导数。它将微分方程离散化为代数系统。稳定性和收敛性依赖于步长。

### Notation
- $u'(x) \approx \frac{u(x+h) - u(x)}{h}$: forward difference
- $\frac{u(x+h) - u(x-h)}{2h}$: centered difference
- $\frac{u(x+h) - 2u(x) + u(x-h)}{h^2}$: second difference
- CFL condition

### Example
- Heat equation: explicit vs implicit schemes
- Wave equation: leapfrog scheme
- Poisson equation: five-point stencil

---

## 3. Finite Element Method (有限元法)

**MSC Code:** 65M60, 65N30

### English Definition
The finite element method solves PDEs by approximating solutions with piecewise polynomial functions on meshes. It uses variational formulations and is particularly effective for complex geometries.

### 中文定义
有限元法通过在网格上用分片多项式函数近似解来求解PDE。它使用变分公式，对复杂几何特别有效。

### Notation
- Mesh $\mathcal{T}_h$ with elements $K$
- Finite element space $V_h$
- Galerkin formulation: find $u_h \in V_h$ such that $a(u_h, v_h) = f(v_h)$ for all $v_h \in V_h$
- Error estimate: $\|u - u_h\| \leq Ch^p$

### Example
- $P_1$ elements on triangles: piecewise linear
- $P_2$ elements: quadratic
- Adaptive mesh refinement

---

## 4. Spectral Method (谱方法)

**MSC Code:** 65M70, 65N35

### English Definition
Spectral methods approximate solutions using global basis functions (Fourier, Chebyshev, Legendre). They achieve exponential convergence for smooth solutions but require regular domains.

### 中文定义
谱方法使用全局基函数（傅里叶、切比雪夫、勒让德）近似解。对光滑解达到指数收敛，但需要正则区域。

### Notation
- Fourier spectral: $\hat{u}_k = \int u(x) e^{-ikx} dx$
- Chebyshev polynomials $T_n(x)$
- Collocation, tau, Galerkin methods

### Example
- Periodic problems: Fourier spectral
- Non-periodic: Chebyshev or Legendre
- Fast convergence for analytic solutions

---

## 5. Linear Programming (线性规划)

**MSC Code:** 90C05

### English Definition
Linear programming optimizes a linear objective function subject to linear constraints. The simplex method and interior point methods are standard solution techniques. Duality theory provides optimality conditions.

### 中文定义
线性规划在优化线性目标函数受线性约束。单纯形法和内点法是标准求解技术。对偶理论提供最优性条件。

### Notation
- Primal: minimize $c^T x$ subject to $Ax = b$, $x \geq 0$
- Dual: maximize $b^T y$ subject to $A^T y \leq c$
- Strong duality: equal optimal values

### Example
- Diet problem
- Transportation problem
- Network flows

---

## 6. Convex Optimization (凸优化)

**MSC Code:** 90C25

### English Definition
Convex optimization minimizes convex functions (or maximizes concave) over convex sets. Local optima are global, and efficient algorithms exist. Includes linear, quadratic, semidefinite, and conic programming.

### 中文定义
凸优化在凸集上最小化凸函数（或最大化凹函数）。局部最优即全局，存在有效算法。包括线性、二次、半定和锥规划。

### Notation
- Convex function: $f(\lambda x + (1-\lambda)y) \leq \lambda f(x) + (1-\lambda)f(y)$
- Convex set: contains line segments
- Gradient descent, Newton's method
- Interior point methods

### Example
- Least squares: $\min \|Ax - b\|^2$
- Support vector machines
- LASSO: $\min \|Ax - b\|^2 + \lambda \|x\|_1$

---

## 7. Nonlinear Programming (非线性规划)

**MSC Code:** 90C30

### English Definition
Nonlinear programming optimizes nonlinear objective functions with nonlinear constraints. The KKT conditions generalize Lagrange multipliers for inequality constraints. Algorithms include SQP, interior point, and trust-region methods.

### 中文定义
非线性规划用非线性约束优化非线性目标函数。KKT条件将拉格朗日乘子推广到不等式约束。算法包括SQP、内点法和信赖域方法。

### Notation
- Minimize $f(x)$ subject to $g_i(x) \leq 0$, $h_j(x) = 0$
- KKT conditions: stationarity, primal feasibility, dual feasibility, complementary slackness
- Lagrangian: $L(x, \lambda, \mu) = f(x) + \sum \lambda_i g_i(x) + \sum \mu_j h_j(x)$

### Example
- Rosenbrock function
- Constrained least squares
- Portfolio optimization

---

## 8. Semidefinite Programming (半定规划)

**MSC Code:** 90C22, 90C25

### English Definition
Semidefinite programming optimizes linear functions over the cone of positive semidefinite matrices. It generalizes linear programming and has applications in control, combinatorics, and quantum information.

### 中文定义
半定规划在正半定矩阵锥上优化线性函数。它推广线性规划，在控制、组合学和量子信息中有应用。

### Notation
- Minimize $\langle C, X \rangle$ subject to $\langle A_i, X \rangle = b_i$, $X \succeq 0$
- $X \succeq 0$: $X$ positive semidefinite
- SDP relaxation of combinatorial problems

### Example
- Max-cut: Goemans-Williamson approximation
- Control: Lyapunov stability
- Sum of squares optimization

---

## 9. Dynamic Programming (动态规划)

**MSC Code:** 90C39, 49L20

### English Definition
Dynamic programming solves optimization problems by breaking them into subproblems and using the principle of optimality. The Bellman equation characterizes optimal value functions.

### 中文定义
动态规划通过将优化问题分解为子问题并使用最优性原理求解。贝尔曼方程刻画最优值函数。

### Notation
- Principle of optimality
- Bellman equation: $V(s) = \min_a \{c(s,a) + \gamma V(s')\}$
- Value iteration, policy iteration
- State, action, reward

### Example
- Shortest path: Dijkstra's algorithm
- Knapsack problem
- Reinforcement learning

---

## 10. Optimal Control Theory (最优控制理论)

**MSC Code:** 49-XX, 93-XX

### English Definition
Optimal control finds control inputs that optimize a cost functional while satisfying dynamics. The Pontryagin maximum principle and Hamilton-Jacobi-Bellman equation are key theoretical tools.

### 中文定义
最优控制寻找在满足动力学的同时优化代价泛函的控制输入。庞特里亚金最大值原理和哈密顿-雅可比-贝尔曼方程是关键理论工具。

### Notation
- State equation: $\dot{x} = f(x, u)$
- Cost functional: $J = \int_0^T L(x, u) dt + \psi(x(T))$
- Hamiltonian: $H(x, p, u) = L(x, u) + p^T f(x, u)$
- Pontryagin's maximum principle

### Example
- Linear-quadratic regulator (LQR)
- Time-optimal control
- Trajectory optimization

---

## 11. Kalman Filter (卡尔曼滤波)

**MSC Code:** 93E11, 60G35

### English Definition
The Kalman filter optimally estimates the state of a linear dynamical system with Gaussian noise. It alternates prediction (state propagation) and update (measurement correction) steps.

### 中文定义
卡尔曼滤波最优估计具有高斯噪声的线性动力系统状态。它交替预测（状态传播）和更新（测量校正）步骤。

### Notation
- Prediction: $\hat{x}_{k|k-1} = F\hat{x}_{k-1|k-1}$, $P_{k|k-1} = FP_{k-1|k-1}F^T + Q$
- Update: $K_k = P_{k|k-1}H^T(HP_{k|k-1}H^T + R)^{-1}$
- $\hat{x}_{k|k} = \hat{x}_{k|k-1} + K_k(z_k - H\hat{x}_{k|k-1})$

### Example
- Navigation and tracking
- Sensor fusion
- Extended Kalman filter for nonlinear systems

---

## 12. System Identification (系统辨识)

**MSC Code:** 93B30, 93E12

### English Definition
System identification builds mathematical models of dynamical systems from input-output data. It includes parameter estimation, model structure selection, and validation.

### 中文定义
系统辨识从输入输出数据建立动力系统的数学模型。它包括参数估计、模型结构选择和验证。

### Notation
- ARX, ARMAX, state-space models
- Prediction error method
- Least squares estimation
- Model order selection (AIC, BIC)

### Example
- Linear regression for ARX models
- Subspace methods (N4SID)
- Neural network models

---

## 13. Robust Control (鲁棒控制)

**MSC Code:** 93B35, 93B36

### English Definition
Robust control designs controllers that maintain performance despite model uncertainty. $H^\infty$ control minimizes the worst-case gain from disturbances to outputs. $\mu$-analysis handles structured uncertainty.

### 中文定义
鲁棒控制设计在模型不确定性下保持性能的控制器。$H^\infty$控制最小化从扰动到输出的最坏情况增益。$\mu$-分析处理结构化不确定性。

### Notation
- $H^\infty$ norm: $\|G\|_\infty = \sup_\omega \sigma_{max}(G(i\omega))$
- Sensitivity $S = (I + PK)^{-1}$
- Complementary sensitivity $T = PK(I + PK)^{-1}$
- Small gain theorem

### Example
- Mixed sensitivity design
- $\mu$-synthesis
- LMI approach to robust control

---

## 14. Model Predictive Control (模型预测控制)

**MSC Code:** 93C55, 49N35

### English Definition
Model predictive control (MPC) solves an optimal control problem over a finite horizon at each time step, applying only the first control action. It handles constraints explicitly and is widely used in industry.

### 中文定义
模型预测控制（MPC）在每个时间步求解有限时域最优控制问题，只应用第一个控制动作。它显式处理约束，在工业中广泛使用。

### Notation
- Receding horizon
- Optimization at each step: $\min_{u} \sum_{k=0}^{N-1} L(x_k, u_k) + V_f(x_N)$
- Constraints: $x_k \in \mathcal{X}$, $u_k \in \mathcal{U}$
- Stability via terminal cost/constraint

### Example
- Process control
- Autonomous vehicles
- Power systems

---

## 15. Neural Network (神经网络)

**MSC Code:** 68T07, 62M45

### English Definition
A neural network is a parameterized function composed of layers of interconnected nodes (neurons). Training optimizes parameters via gradient descent on a loss function. Universal approximation theorems guarantee expressiveness.

### 中文定义
神经网络是由相互连接的节点（神经元）层组成的参数化函数。训练通过损失函数上的梯度下降优化参数。通用近似定理保证表达能力。

### Notation
- Layer: $x^{(l+1)} = \sigma(W^{(l)}x^{(l)} + b^{(l)})$
- Activation $\sigma$: ReLU, sigmoid, tanh
- Loss function: MSE, cross-entropy
- Backpropagation

### Example
- Feedforward networks
- CNNs for images
- RNNs/LSTMs for sequences
- Transformers

---

## 16. Deep Learning (深度学习)

**MSC Code:** 68T07, 68T45

### English Definition
Deep learning uses neural networks with many layers to learn hierarchical representations from data. It has achieved breakthrough results in computer vision, natural language processing, and games.

### 中文定义
深度学习使用多层神经网络从数据学习层次表示。它在计算机视觉、自然语言处理和游戏中取得突破性成果。

### Notation
- Deep networks: many hidden layers
- Convolution, pooling, batch normalization
- Dropout, regularization
- Optimization: SGD, Adam, etc.

### Example
- ImageNet classification
- GPT language models
- AlphaGo/AlphaZero

---

## 17. Optimization Algorithm (优化算法)

**MSC Code:** 90C52, 90C53, 68W40

### English Definition
Optimization algorithms find minima or maxima of functions. Gradient-based methods use first-order information; Newton-type methods use second-order. Stochastic methods handle large-scale and online settings.

### 中文定义
优化算法寻找函数的极小值或极大值。基于梯度的方法使用一阶信息；牛顿型方法使用二阶。随机方法处理大规模和在线设置。

### Notation
- Gradient descent: $x_{k+1} = x_k - \alpha \nabla f(x_k)$
- Newton: $x_{k+1} = x_k - [\nabla^2 f(x_k)]^{-1}\nabla f(x_k)$
- SGD: $x_{k+1} = x_k - \alpha g_k$ with stochastic gradient $g_k$

### Example
- Conjugate gradient
- Quasi-Newton (BFGS)
- Adam, RMSprop

---

## 18. Regularization (正则化)

**MSC Code:** 65F22, 65F20, 62J07

### English Definition
Regularization prevents overfitting by adding penalty terms to the objective or constraining the solution space. Common forms include L2 (Tikhonov/ridge), L1 (lasso), and early stopping.

### 中文定义
正则化通过向目标添加惩罚项或约束解空间来防止过拟合。常见形式包括L2（吉洪诺夫/岭）、L1（lasso）和早停。

### Notation
- Tikhonov: $\min \|Ax - b\|^2 + \lambda \|x\|^2$
- LASSO: $\min \|Ax - b\|^2 + \lambda \|x\|_1$
- Elastic net: combination of L1 and L2

### Example
- Ill-posed inverse problems
- Feature selection
- Neural network training

---

## 19. Monte Carlo Method (蒙特卡洛方法)

**MSC Code:** 65C05, 65Cxx

### English Definition
Monte Carlo methods use random sampling to estimate quantities of interest. They are particularly effective for high-dimensional integration and problems with complex geometry.

### 中文定义
蒙特卡洛方法使用随机抽样估计感兴趣的量。它对高维积分和复杂几何问题特别有效。

### Notation
- $\mathbb{E}[f(X)] \approx \frac{1}{N}\sum_{i=1}^N f(X_i)$
- Variance reduction: importance sampling, control variates
- Markov Chain Monte Carlo (MCMC)

### Example
- Estimating $\pi$
- Option pricing
- Bayesian inference (MCMC)

---

## 20. Information Theory (信息论)

**MSC Code:** 94A15, 94Axx

### English Definition
Information theory quantifies information content, storage, and transmission. Key concepts include entropy (uncertainty), mutual information (dependence), and channel capacity (maximum reliable transmission rate).

### 中文定义
信息论量化信息内容、存储和传输。关键概念包括熵（不确定性）、互信息（依赖性）和信道容量（最大可靠传输速率）。

### Notation
- Shannon entropy: $H(X) = -\sum p(x) \log p(x)$
- Mutual information: $I(X;Y) = H(X) - H(X|Y)$
- Channel capacity: $C = \max_{p(x)} I(X;Y)$
- KL divergence: $D_{KL}(P\|Q) = \sum p(x) \log \frac{p(x)}{q(x)}$

### Example
- Source coding: Huffman coding
- Channel coding: Shannon's noisy channel theorem
- Applications in machine learning (cross-entropy loss)

---

*End of Applied Mathematics Concepts*
