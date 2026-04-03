# MIT 18.337J: 科学机器学习课程笔记

> MIT 18.337J - Introduction to Numerical Computing and Scientific Machine Learning
> 讲师: Prof. Steven G. Johnson

---

## 课程概述

### 课程目标

1. 理解现代科学计算的基本原理
2. 掌握Julia语言进行高性能计算
3. 学习科学机器学习的核心概念：
   - 物理信息神经网络 (PINNs)
   - 神经微分方程
   - 可微分编程
   - 神经算子

### 先修要求

- 线性代数
- 微积分和常微分方程
- 基础编程经验
- 数值方法基础（推荐）

---

## 第一部分：Julia编程与高性能计算

### 第1讲：Julia语言入门

**Julia的设计哲学**

```julia
# Julia的关键特性

# 1. 多重派发 (Multiple Dispatch)
struct Point{T}
    x::T
    y::T
end

# 基于类型的函数选择
distance(p::Point) = sqrt(p.x^2 + p.y^2)
distance(p1::Point, p2::Point) = sqrt((p1.x-p2.x)^2 + (p1.y-p2.y)^2)

# 2. 元编程
macro timeit(expr)
    quote
        t0 = time()
        val = $(esc(expr))
        println("Elapsed time: ", time() - t0, " seconds")
        val
    end
end

# 3. 广播操作
A = rand(1000, 1000)
B = rand(1000, 1000)
C = A .* B  # 逐元素乘法，自动SIMD优化
```

**性能优化**

```julia
# 类型稳定性的重要性
function slow_sum(x)
    s = 0  # s初始化为Int
    for i in eachindex(x)
        s += x[i]  # 如果x是Float64，这里会类型转换
    end
    return s
end

function fast_sum(x::Vector{T}) where T
    s = zero(T)  # 确保类型稳定
    @inbounds for i in eachindex(x)
        s += x[i]
    end
    return s
end

# 使用@code_warntype检查类型稳定性
```

### 第2讲：自动微分

**前向模式与反向模式**

```julia
using ForwardDiff, Zygote

# 前向模式：适合f: R^n → R^m，n较小
f(x) = [x[1]^2 + x[2]^2, x[1]*x[2]]
J_forward = ForwardDiff.jacobian(f, [1.0, 2.0])

# 反向模式：适合f: R^n → R，n较大
loss(x) = sum(x.^2)
grad_reverse = Zygote.gradient(loss, rand(1000))

# 自定义梯度
using ChainRulesCore

function my_function(x)
    # 前向计算
    return complex_operation(x)
end

function ChainRulesCore.rrule(::typeof(my_function), x)
    y = my_function(x)
    function pullback(ȳ)
        # 反向传播规则
        return NoTangent(), custom_gradient(x, ȳ)
    end
    return y, pullback
end
```

**Hessian和更高阶导数**

```julia
# Hessian矩阵
f(x) = x[1]^4 + x[2]^4 + x[1]*x[2]
H = ForwardDiff.hessian(f, [1.0, 2.0])

# 混合模式：高效率Hessian-vector积
using LinearAlgebra

function hvp(f, x, v)
    # Hessian-vector product
    return ForwardDiff.derivative(t -> Zygote.gradient(f, x + t*v)[1], 0.0)
end
```

### 第3讲：微分方程求解

**DifferentialEquations.jl基础**

```julia
using DifferentialEquations

# 定义ODE问题
function lorenz!(du, u, p, t)
    σ, ρ, β = p
    du[1] = σ*(u[2]-u[1])
    du[2] = u[1]*(ρ-u[3]) - u[2]
    du[3] = u[1]*u[2] - β*u[3]
end

u0 = [1.0, 0.0, 0.0]
tspan = (0.0, 100.0)
p = [10.0, 28.0, 8/3]

prob = ODEProblem(lorenz!, u0, tspan, p)
sol = solve(prob, Tsit5(), reltol=1e-8, abstol=1e-8)

# 灵敏度分析
using ForwardDiff

function solve_with_params(p)
    prob = ODEProblem(lorenz!, u0, tspan, p)
    sol = solve(prob, Tsit5(), saveat=0.1)
    return sol.u[end][1]  # 返回最终x值
end

# 计算关于参数的梯度
∂f_∂p = ForwardDiff.gradient(solve_with_params, p)
```

**事件处理与回调**

```julia
# 定义事件
condition(u, t, integrator) = u[1] - 2.0  # 当x=2时触发

function affect!(integrator)
    integrator.u[2] *= 0.9  # y速度减小10%
end

cb = ContinuousCallback(condition, affect!)

sol = solve(prob, Tsit5(), callback=cb)
```

---

## 第二部分：物理信息神经网络

### 第4讲：PINNs理论基础

**核心概念**

PINNs的损失函数组成：
$$\mathcal{L} = \mathcal{L}_{\text{PDE}} + \mathcal{L}_{\text{BC}} + \mathcal{L}_{\text{IC}} + \mathcal{L}_{\text{data}}$$

**Julia实现**

```julia
using Flux, Zygote

struct PINN{M,P}
    network::M
    params::P
end

# 创建网络
function create_pynn(input_dim, hidden_dim, output_dim, n_layers)
    layers = []
    push!(layers, Dense(input_dim, hidden_dim, tanh))
    for _ in 1:n_layers-1
        push!(layers, Dense(hidden_dim, hidden_dim, tanh))
    end
    push!(layers, Dense(hidden_dim, output_dim))
    return Chain(layers...)
end

# 自动微分计算PDE残差
function pde_residual(model, x, t, nu)
    xt = hcat(x, t)
    u = model(xt)
    
    # 计算导数
    u_t = Zygote.gradient(xt -> sum(model(xt)), xt)[1][:, 2]
    u_x = Zygote.gradient(xt -> sum(model(xt)), xt)[1][:, 1]
    u_xx = Zygote.gradient(x -> sum(
        Zygote.gradient(xt -> sum(model(xt)), hcat(x, t))[1][:, 1]
    ), x)[1]
    
    # Burgers方程残差: u_t + u*u_x - nu*u_xx = 0
    return u_t + u.*u_x - nu*u_xx
end
```

### 第5讲：PINNs高级主题

**自适应损失平衡**

```julia
# 使用梯度统计的自适应权重
function compute_adaptive_weights(model, x_f, t_f, x_bc, t_bc, u_bc)
    # 计算各损失的梯度范数
    grad_f = Zygote.gradient(() -> loss_pde(model, x_f, t_f), Flux.params(model))
    grad_bc = Zygote.gradient(() -> loss_bc(model, x_bc, t_bc, u_bc), Flux.params(model))
    
    # 自适应权重
    λ_f = 1.0 / mean([norm(g) for g in grad_f])
    λ_bc = 1.0 / mean([norm(g) for g in grad_bc])
    
    return λ_f, λ_bc
end

# 学习率退火
function lr_schedule(epoch, max_epochs)
    return 1e-3 * (0.9 ^ (epoch ÷ 1000))
end
```

**因果训练**

```julia
# 对于时间依赖问题，使用因果训练
function causal_loss(model, x, t, nu, epsilon=1e-5)
    n_time = length(unique(t))
    causal_weights = ones(n_time)
    
    total_loss = 0.0
    for i in 1:n_time
        mask = (t .== sorted_times[i])
        residual = pde_residual(model, x[mask], t[mask], nu)
        loss_i = mean(residual.^2)
        
        # 累积因果权重
        if i > 1 && loss_i > epsilon
            causal_weights[i:end] .*= exp(-loss_i)
        end
        
        total_loss += causal_weights[i] * loss_i
    end
    
    return total_loss
end
```

---

## 第三部分：神经微分方程

### 第6讲：神经ODE基础

**概念**

将神经网络层看作连续时间的ODE：
$$\frac{dh(t)}{dt} = f(h(t), t, \theta)$$

**DiffEqFlux.jl实现**

```julia
using DifferentialEquations, DiffEqFlux, Flux, Optimization

# 定义神经ODE
dudt = Flux.Chain(
    Flux.Dense(2, 50, tanh),
    Flux.Dense(50, 2)
)

# 包装为ODE函数
function neural_ode(u, p, t)
    return dudt(u)
end

# 创建ODE问题
u0 = Float32[2.0, 0.0]
tspan = (0.0f0, 1.0f0)
prob = ODEProblem(neural_ode, u0, tspan)

# 预测函数
function predict(p)
    _prob = remake(prob, p=p)
    sol = solve(_prob, Tsit5(), saveat=0.1)
    return Array(sol)
end

# 损失函数
function loss(p)
    pred = predict(p)
    return sum(abs2, pred .- true_data)
end

# 训练
optf = Optimization.OptimizationFunction((x, p) -> loss(x), Optimization.AutoZygote())
optprob = Optimization.OptimizationProblem(optf, p_init)
result = Optimization.solve(optprob, ADAM(0.05), maxiters=300)
```

### 第7讲：神经ODE应用

**时间序列预测**

```julia
using DiffEqFlux, Flux

# Latent ODE模型
encoder = Chain(
    Dense(1, 50, relu),
    Dense(50, 20)
)

latent_dynamics = Chain(
    Dense(20, 50, tanh),
    Dense(50, 20)
)

decoder = Chain(
    Dense(20, 50, relu),
    Dense(50, 1)
)

function latent_ode_forward(x0, t)
    # 编码
    z0 = encoder(x0)
    
    # 在隐空间中解ODE
    function dynamics(z, p, t)
        return latent_dynamics(z)
    end
    
    prob = ODEProblem(dynamics, z0, (t[1], t[end]))
    sol = solve(prob, Tsit5(), saveat=t)
    
    # 解码
    return decoder.(sol.u)
end
```

**正则化化流**

```julia
using DiffEqFlux, Distributions

# 连续归一化流
nn = Flux.Chain(
    Dense(2 + 1, 64, tanh),  # +1 for time
    Dense(64, 64, tanh),
    Dense(64, 2)
)

function cnf(u, p, t)
    return nn(vcat(u, [t]))
end

# 训练
function logpdf_cnf(x, model)
    # 从数据分布变换到先验
    function augmented_dynamics(u, p, t)
        z = u[1:end-1]
        dz = model(z, p, t)
        # 计算迹
        trace_jacobian = tr(jacobian(z -> model(z, p, t), z))
        return vcat(dz, -trace_jacobian)
    end
    
    u0 = vcat(x, [0.0])
    prob = ODEProblem(augmented_dynamics, u0, (0.0, 1.0))
    sol = solve(prob, Tsit5())
    
    z1 = sol.u[end][1:end-1]
    log_det = sol.u[end][end]
    
    # 标准高斯先验的对数概率
    log_pz = logpdf(MvNormal(zeros(2), I), z1)
    
    return log_pz + log_det
end
```

---

## 第四部分：神经算子

### 第8讲：神经算子理论

**核心概念**

学习算子 $G^\dagger: \mathcal{A} \to \mathcal{U}$，其中输入和输出都是函数。

**Fourier神经算子 (FNO)**

```julia
using Flux, FFTW

# 谱卷积层
struct SpectralConv{N}
    weights::Array{ComplexF32, N}
    modes::NTuple{N, Int}
end

Flux.@layer SpectralConv

function (layer::SpectralConv)(x)
    # FFT
    x_ft = fft(x, 2:ndims(x))
    
    # 乘以低模式权重
    out_ft = zero(x_ft)
    inds = [1:m for m in layer.modes]
    out_ft[inds..., :] = x_ft[inds..., :] .* layer.weights
    
    # IFFT
    return real(ifft(out_ft, 2:ndims(x)))
end

# FNO架构
FNO = Chain(
    # 提升到高维空间
    Conv((1,), 1 => 32),
    
    # Fourier层
    SkipConnection(Chain(
        SpectralConv(32, (16,)),
        x -> relu.(x)
    ), +),
    SkipConnection(Chain(
        SpectralConv(32, (16,)),
        x -> relu.(x)
    ), +),
    SkipConnection(Chain(
        SpectralConv(32, (16,)),
        x -> relu.(x)
    ), +),
    SkipConnection(Chain(
        SpectralConv(32, (16,)),
    ), +),
    
    # 投影回输出空间
    Conv((1,), 32 => 1)
)
```

### 第9讲：神经算子应用

**Darcy流问题**

```julia
using Flux, HDF5

# 数据加载
function load_darcy_data(filename)
    h5open(filename, "r") do file
        a = read(file, "input")  # 渗透率场
        u = read(file, "output") # 压力场
        return a, u
    end
end

# 训练循环
function train_fno(model, train_loader, epochs=500)
    opt_state = Flux.setup(Adam(1e-3), model)
    
    for epoch in 1:epochs
        losses = []
        for (a, u) in train_loader
            loss, grads = Flux.withgradient(model) do m
                u_pred = m(a)
                Flux.mse(u_pred, u)
            end
            
            Flux.update!(opt_state, model, grads[1])
            push!(losses, loss)
        end
        
        if epoch % 10 == 0
            println("Epoch $epoch, Loss: $(mean(losses))")
        end
    end
    
    return model
end
```

---

## 第五部分：高级主题

### 第10讲：不确定性量化

**贝叶斯神经网络**

```julia
using Turing, DifferentialEquations

# 贝叶斯PINN
@model function bayesian_pinn(x, t, u_obs, nu)
    # 先验分布
    W1 ~ MvNormal(zeros(32), I)
    b1 ~ MvNormal(zeros(32), I)
    W2 ~ MvNormal(zeros(1), I)
    b2 ~ Normal(0, 1)
    σ ~ InverseGamma(2, 3)  # 观测噪声
    
    # 神经网络
    h = tanh.(x .* W1 .+ t .* W1 .+ b1)
    u_pred = h'W2 .+ b2
    
    # 似然
    u_obs ~ MvNormal(u_pred, σ^2 * I)
end

# MCMC采样
chain = sample(bayesian_pinn(x, t, u_obs, 0.01), NUTS(), MCMCThreads(), 1000, 4)
```

### 第11讲：多尺度与多物理场

**多尺度PINNs**

```julia
# 使用多个网络处理不同尺度
macro_network = Chain(...)  # 宏观行为
micro_network = Chain(...)  # 微观行为

function multiscale_pinn(x, t)
    u_macro = macro_network([x, t])
    u_micro = micro_network([x/epsilon, t/epsilon])
    return u_macro + epsilon * u_micro
end
```

### 第12讲：可微分编程实战

**端到端可微的物理模拟**

```julia
using ChainRulesCore, Zygote

# 可微分物理引擎
function physics_step(state, action, dt)
    # 物理模拟前向传播
    new_state = simulate(state, action, dt)
    return new_state
end

# 定义反向传播规则
function ChainRulesCore.rrule(::typeof(physics_step), state, action, dt)
    new_state = physics_step(state, action, dt)
    
    function physics_pullback(new_statē)
        # 使用伴随法计算梯度
        # ...
        return NoTangent(), statē, action̄, NoTangent()
    end
    
    return new_state, physics_pullback
end

# 现在可以端到端训练
params = init_params()
for epoch in 1:1000
    loss, grads = Zygote.withgradient(params) do p
        state = initial_state
        for t in 1:T
            action = policy(state, p)
            state = physics_step(state, action, dt)
        end
        return final_cost(state)
    end
    
    params -= lr * grads[1]
end
```

---

## 附录：Julia/SciML工具链

### 核心包

| 包名 | 用途 | 示例 |
|-----|------|------|
| DifferentialEquations.jl | 微分方程求解 | `solve(prob, Tsit5())` |
| DiffEqFlux.jl | 神经微分方程 | `NeuralODE(chain)` |
| Flux.jl | 深度学习 | `Chain(Dense(...))` |
| Zygote.jl | 自动微分 | `gradient(f, x)` |
| ForwardDiff.jl | 前向自动微分 | `jacobian(f, x)` |
| Optim.jl | 优化 | `optimize(f, x0, LBFGS())` |
| Turing.jl | 概率编程 | `@model ...` |
| FFTW.jl | 快速傅里叶变换 | `fft(x)` |

### 学习资源

1. **Julia文档**: https://docs.julialang.org/
2. **SciML教程**: https://tutorials.sciml.ai/
3. **DiffEqFlux文档**: https://diffeqflux.sciml.ai/
4. **课程网站**: https://github.com/mitmath/18337

---

*课程笔记整理: 2026年4月 | FormalMath项目*
