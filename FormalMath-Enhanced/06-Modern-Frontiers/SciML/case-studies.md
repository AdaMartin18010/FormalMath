---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# 科学机器学习：案例研究

> 物理信息神经网络、神经微分方程和神经算子的实际应用案例

---

## 1. 物理信息神经网络 (PINNs) 案例

### 1.1 案例一：Burgers方程求解

**问题描述**:

Burgers方程是流体力学中的非线性偏微分方程：
$$\frac{\partial u}{\partial t} + u\frac{\partial u}{\partial x} = \nu \frac{\partial^2 u}{\partial x^2}$$

其中 $\nu$ 是粘性系数。

**PINN架构**:

```python
import torch
import torch.nn as nn
import numpy as np

class BurgersPINN(nn.Module):
    def __init__(self, layers=[2, 50, 50, 50, 1]):
        super().__init__()

        # 构建网络
        self.network = nn.Sequential()
        for i in range(len(layers) - 1):
            self.network.add_module(f'layer_{i}', nn.Linear(layers[i], layers[i+1]))
            if i < len(layers) - 2:
                self.network.add_module(f'tanh_{i}', nn.Tanh())

    def forward(self, x, t):
        """前向传播"""
        inputs = torch.cat([x, t], dim=1)
        return self.network(inputs)

    def pde_residual(self, x, t, nu=0.01/np.pi):
        """计算PDE残差"""
        x.requires_grad_(True)
        t.requires_grad_(True)

        u = self.forward(x, t)

        # 自动微分计算导数
        u_t = torch.autograd.grad(u, t, grad_outputs=torch.ones_like(u),
                                   create_graph=True)[0]
        u_x = torch.autograd.grad(u, x, grad_outputs=torch.ones_like(u),
                                   create_graph=True)[0]
        u_xx = torch.autograd.grad(u_x, x, grad_outputs=torch.ones_like(u_x),
                                    create_graph=True)[0]

        # Burgers方程残差
        residual = u_t + u * u_x - nu * u_xx
        return residual

# 训练函数
def train_burgers_pinn(model, x_f, t_f, x_ic, t_ic, u_ic, x_bc, t_bc, u_bc, epochs=10000):
    """
    训练Burgers PINN

    参数:
    - x_f, t_f: 配点坐标（内部）
    - x_ic, t_ic, u_ic: 初始条件数据
    - x_bc, t_bc, u_bc: 边界条件数据
    """
    optimizer = torch.optim.Adam(model.parameters(), lr=1e-3)

    for epoch in range(epochs):
        optimizer.zero_grad()

        # PDE残差损失
        res = model.pde_residual(x_f, t_f)
        loss_f = torch.mean(res**2)

        # 初始条件损失
        u_pred_ic = model.forward(x_ic, t_ic)
        loss_ic = torch.mean((u_pred_ic - u_ic)**2)

        # 边界条件损失
        u_pred_bc = model.forward(x_bc, t_bc)
        loss_bc = torch.mean((u_pred_bc - u_bc)**2)

        # 总损失
        loss = loss_f + loss_ic + loss_bc

        loss.backward()
        optimizer.step()

        if epoch % 1000 == 0:
            print(f"Epoch {epoch}, Loss: {loss.item():.6f}")

    return model
```

**结果**:

- 在粗网格上训练，可以在细网格上预测
- 相对L2误差 < 1%
- 无需传统数值方法的离散化

### 1.2 案例二：逆问题 - 热传导系数识别

**问题设置**:

热方程：$\frac{\partial u}{\partial t} = k \frac{\partial^2 u}{\partial x^2}$

目标：从观测数据中识别未知的热传导系数 $k$。

**PINN实现**:

```python
class InverseHeatPINN(nn.Module):
    def __init__(self):
        super().__init__()
        self.network = nn.Sequential(
            nn.Linear(2, 50),
            nn.Tanh(),
            nn.Linear(50, 50),
            nn.Tanh(),
            nn.Linear(50, 1)
        )
        # 待识别的参数
        self.k = nn.Parameter(torch.tensor([0.5], dtype=torch.float32))

    def forward(self, x, t):
        inputs = torch.cat([x, t], dim=1)
        return self.network(inputs)

    def pde_residual(self, x, t):
        x.requires_grad_(True)
        t.requires_grad_(True)

        u = self.forward(x, t)
        u_t = torch.autograd.grad(u, t, grad_outputs=torch.ones_like(u),
                                   create_graph=True)[0]
        u_x = torch.autograd.grad(u, x, grad_outputs=torch.ones_like(u),
                                   create_graph=True)[0]
        u_xx = torch.autograd.grad(u_x, x, grad_outputs=torch.ones_like(u_x),
                                    create_graph=True)[0]

        # 使用待识别的k
        return u_t - self.k * u_xx

# 训练过程同时优化网络参数和物理参数
def train_inverse_pinn(model, x_obs, t_obs, u_obs, x_f, t_f, epochs=20000):
    optimizer = torch.optim.Adam(model.parameters(), lr=1e-3)

    for epoch in range(epochs):
        optimizer.zero_grad()

        # 数据拟合损失
        u_pred = model.forward(x_obs, t_obs)
        loss_data = torch.mean((u_pred - u_obs)**2)

        # PDE约束损失
        res = model.pde_residual(x_f, t_f)
        loss_pde = torch.mean(res**2)

        loss = loss_data + loss_pde
        loss.backward()
        optimizer.step()

        if epoch % 2000 == 0:
            print(f"Epoch {epoch}, Loss: {loss.item():.6f}, k: {model.k.item():.4f}")

    return model.k.item()
```

**结果**:

- 真实值 $k = 0.5$，识别结果 $k \approx 0.498$
- 同时获得解的完整时空分布

### 1.3 案例三：Navier-Stokes方程

**问题**: 2D不可压Navier-Stokes方程

```python
class NavierStokesPINN(nn.Module):
    def __init__(self, Re=100):
        super().__init__()
        self.Re = Re
        # 两个网络分别输出u, v, p
        self.net_uv = self._build_network(3, [50, 50, 50, 2])  # u, v
        self.net_p = self._build_network(3, [50, 50, 50, 1])   # p

    def _build_network(self, input_dim, layer_dims):
        layers = []
        prev_dim = input_dim
        for dim in layer_dims[:-1]:
            layers.extend([nn.Linear(prev_dim, dim), nn.Tanh()])
            prev_dim = dim
        layers.append(nn.Linear(prev_dim, layer_dims[-1]))
        return nn.Sequential(*layers)

    def forward(self, x, y, t):
        inputs = torch.cat([x, y, t], dim=1)
        uv = self.net_uv(inputs)
        u, v = uv[:, 0:1], uv[:, 1:2]
        p = self.net_p(inputs)
        return u, v, p

    def pde_residual(self, x, y, t):
        x.requires_grad_(True)
        y.requires_grad_(True)
        t.requires_grad_(True)

        u, v, p = self.forward(x, y, t)

        # 一阶导数
        u_t = torch.autograd.grad(u, t, grad_outputs=torch.ones_like(u),
                                   create_graph=True)[0]
        u_x = torch.autograd.grad(u, x, grad_outputs=torch.ones_like(u),
                                   create_graph=True)[0]
        u_y = torch.autograd.grad(u, y, grad_outputs=torch.ones_like(u),
                                   create_graph=True)[0]

        v_t = torch.autograd.grad(v, t, grad_outputs=torch.ones_like(v),
                                   create_graph=True)[0]
        v_x = torch.autograd.grad(v, x, grad_outputs=torch.ones_like(v),
                                   create_graph=True)[0]
        v_y = torch.autograd.grad(v, y, grad_outputs=torch.ones_like(v),
                                   create_graph=True)[0]

        p_x = torch.autograd.grad(p, x, grad_outputs=torch.ones_like(p),
                                   create_graph=True)[0]
        p_y = torch.autograd.grad(p, y, grad_outputs=torch.ones_like(p),
                                   create_graph=True)[0]

        # 二阶导数
        u_xx = torch.autograd.grad(u_x, x, grad_outputs=torch.ones_like(u_x),
                                    create_graph=True)[0]
        u_yy = torch.autograd.grad(u_y, y, grad_outputs=torch.ones_like(u_y),
                                    create_graph=True)[0]
        v_xx = torch.autograd.grad(v_x, x, grad_outputs=torch.ones_like(v_x),
                                    create_graph=True)[0]
        v_yy = torch.autograd.grad(v_y, y, grad_outputs=torch.ones_like(v_y),
                                    create_graph=True)[0]

        # NS方程残差
        f_u = u_t + u*u_x + v*u_y + p_x - (u_xx + u_yy) / self.Re
        f_v = v_t + u*v_x + v*v_y + p_y - (v_xx + v_yy) / self.Re

        # 连续性方程
        f_cont = u_x + v_y

        return f_u, f_v, f_cont
```

---

## 2. 神经微分方程应用

### 2.1 案例一：时间序列预测

**神经ODE用于学习连续时间动态**:

```python
import torch
from torchdiffeq import odeint

class NeuralODETimeSeries(nn.Module):
    def __init__(self, hidden_dim=20):
        super().__init__()
        # 定义ODE的动力学
        self.dynamics = nn.Sequential(
            nn.Linear(hidden_dim, 50),
            nn.ReLU(),
            nn.Linear(50, hidden_dim)
        )

        # 编码器和解码器
        self.encoder = nn.Linear(1, hidden_dim)
        self.decoder = nn.Linear(hidden_dim, 1)

    def forward(self, t, x):
        """ODE的右端项"""
        return self.dynamics(x)

    def predict(self, t_obs, x_obs, t_pred):
        """
        预测未来值

        参数:
        - t_obs: 观测时间点
        - x_obs: 观测值
        - t_pred: 预测时间点
        """
        # 编码初始条件
        h0 = self.encoder(x_obs[0:1])

        # 求解ODE
        h_pred = odeint(self, h0, t_pred, method='dopri5')

        # 解码
        x_pred = self.decoder(h_pred)
        return x_pred

# 训练
def train_neural_ode(model, t_train, x_train, epochs=1000):
    optimizer = torch.optim.Adam(model.parameters(), lr=0.01)

    for epoch in range(epochs):
        optimizer.zero_grad()

        # 编码
        h0 = model.encoder(x_train[0:1])

        # 前向ODE求解
        h_pred = odeint(model, h0, t_train, method='dopri5')
        x_pred = model.decoder(h_pred)

        # 损失
        loss = torch.mean((x_pred - x_train)**2)

        loss.backward()
        optimizer.step()

        if epoch % 100 == 0:
            print(f"Epoch {epoch}, Loss: {loss.item():.6f}")
```

### 2.2 案例二：生成模型 - 神经ODEFlows

**连续归一化流**:

```python
class ODENormalizingFlow(nn.Module):
    def __init__(self, dim=2):
        super().__init__()
        self.dim = dim

        # 神经网络定义向量场
        self.net = nn.Sequential(
            nn.Linear(dim + 1, 64),  # +1 for time
            nn.Softplus(),
            nn.Linear(64, 64),
            nn.Softplus(),
            nn.Linear(64, dim)
        )

    def forward(self, t, x):
        """向量场 f(t, x)"""
        t_expanded = t.expand(x.shape[0], 1)
        tx = torch.cat([t_expanded, x], dim=1)
        return self.net(tx)

    def trace_dfdx(self, t, x):
        """计算雅可比迹（用于体积变化）"""
        with torch.enable_grad():
            x.requires_grad_(True)
            f = self.forward(t, x)

            # 计算雅可比的对角线元素
            divergence = torch.zeros(x.shape[0]).to(x)
            for i in range(self.dim):
                divergence += torch.autograd.grad(
                    f[:, i].sum(), x, create_graph=True
                )[0][:, i]

            return divergence

    def log_prob(self, x, integration_times=None):
        """
        计算对数概率

        从数据分布变换到先验（标准高斯）
        """
        if integration_times is None:
            integration_times = torch.tensor([0.0, 1.0]).to(x)

        # 增强状态以跟踪对数行列式
        log_det = torch.zeros(x.shape[0], 1).to(x)
        z0_logdet = torch.cat([x, log_det], dim=1)

        # 定义增强ODE
        def augmented_dynamics(t, z):
            x = z[:, :-1]
            with torch.set_grad_enabled(True):
                dx = self.forward(t, x)
                divergence = self.trace_dfdx(t, x).unsqueeze(1)
            return torch.cat([dx, -divergence], dim=1)

        # 积分
        zt = odeint(augmented_dynamics, z0_logdet, integration_times,
                    method='dopri5', atol=1e-5, rtol=1e-5)

        z1 = zt[-1, :, :-1]
        log_det_jacobian = zt[-1, :, -1]

        # 先验的对数概率（标准高斯）
        log_pz1 = -0.5 * (z1**2).sum(dim=1) - 0.5 * self.dim * np.log(2 * np.pi)

        # 变量替换公式
        log_px = log_pz1 + log_det_jacobian

        return log_px

# 训练生成模型
def train_flow(model, data_loader, epochs=100):
    optimizer = torch.optim.Adam(model.parameters(), lr=1e-3)

    for epoch in range(epochs):
        total_loss = 0
        for batch in data_loader:
            optimizer.zero_grad()

            # 最大化对数似然
            log_prob = model.log_prob(batch)
            loss = -log_prob.mean()

            loss.backward()
            optimizer.step()

            total_loss += loss.item()

        print(f"Epoch {epoch}, Loss: {total_loss / len(data_loader):.4f}")
```

### 2.3 案例三：神经SDE - 随机动力学

```python
import torchsde

class NeuralSDE(torchsde.SDEIto):
    def __init__(self, state_dim=2):
        super().__init__(noise_type="diagonal")
        self.state_dim = state_dim

        # 漂移项
        self.drift_net = nn.Sequential(
            nn.Linear(state_dim, 50),
            nn.ReLU(),
            nn.Linear(50, state_dim)
        )

        # 扩散项
        self.diffusion_net = nn.Sequential(
            nn.Linear(state_dim, 50),
            nn.ReLU(),
            nn.Linear(50, state_dim),
            nn.Softplus()  # 保证非负
        )

    def f(self, t, y):
        """漂移系数"""
        return self.drift_net(y)

    def g(self, t, y):
        """扩散系数"""
        return self.diffusion_net(y)

# 训练
def train_neural_sde(sde, ys, ts, epochs=1000):
    optimizer = torch.optim.Adam(sde.parameters(), lr=1e-2)

    for epoch in range(epochs):
        optimizer.zero_grad()

        # 求解SDE
        y0 = ys[0]
        ys_pred = torchsde.sdeint(sde, y0, ts, method='euler')

        # 损失
        loss = torch.mean((ys_pred - ys)**2)

        loss.backward()
        optimizer.step()

        if epoch % 100 == 0:
            print(f"Epoch {epoch}, Loss: {loss.item():.6f}")
```

---

## 3. 神经算子实例

### 3.1 案例一：Darcy流 - Fourier神经算子

**问题**: 学习从渗透率场到压力场的映射

```python
import torch
import torch.nn as nn
import torch.nn.functional as F

class SpectralConv2d(nn.Module):
    """傅里叶空间中的谱卷积"""
    def __init__(self, in_channels, out_channels, modes1, modes2):
        super().__init__()
        self.in_channels = in_channels
        self.out_channels = out_channels
        self.modes1 = modes1  # 傅里叶模式数x
        self.modes2 = modes2  # 傅里叶模式数y

        # 复数权重
        self.weights1 = nn.Parameter(
            torch.rand(in_channels, out_channels, modes1, modes2, 2) * 0.05
        )
        self.weights2 = nn.Parameter(
            torch.rand(in_channels, out_channels, modes1, modes2, 2) * 0.05
        )

    def compl_mul2d(self, input, weights):
        """复数乘法"""
        return torch.einsum("bixy,ioxy->boxy", input, weights)

    def forward(self, x):
        batchsize = x.shape[0]

        # FFT
        x_ft = torch.fft.rfft2(x)

        # 乘以相关傅里叶模式
        out_ft = torch.zeros(batchsize, self.out_channels, x.size(-2), x.size(-1)//2 + 1,
                            dtype=torch.cfloat, device=x.device)

        out_ft[:, :, :self.modes1, :self.modes2] = self.compl_mul2d(
            x_ft[:, :, :self.modes1, :self.modes2],
            torch.view_as_complex(self.weights1)
        )
        out_ft[:, :, -self.modes1:, :self.modes2] = self.compl_mul2d(
            x_ft[:, :, -self.modes1:, :self.modes2],
            torch.view_as_complex(self.weights2)
        )

        # IFFT
        x = torch.fft.irfft2(out_ft, s=(x.size(-2), x.size(-1)))
        return x

class FNO2d(nn.Module):
    """2D Fourier神经算子"""
    def __init__(self, modes1, modes2, width):
        super().__init__()
        self.modes1 = modes1
        self.modes2 = modes2
        self.width = width

        # 输入提升
        self.fc0 = nn.Linear(3, width)  # a(x,y), x, y -> width

        # 傅里叶层
        self.conv0 = SpectralConv2d(width, width, modes1, modes2)
        self.conv1 = SpectralConv2d(width, width, modes1, modes2)
        self.conv2 = SpectralConv2d(width, width, modes1, modes2)
        self.conv3 = SpectralConv2d(width, width, modes1, modes2)

        self.w0 = nn.Conv2d(width, width, 1)
        self.w1 = nn.Conv2d(width, width, 1)
        self.w2 = nn.Conv2d(width, width, 1)
        self.w3 = nn.Conv2d(width, width, 1)

        # 输出投影
        self.fc1 = nn.Linear(width, 128)
        self.fc2 = nn.Linear(128, 1)

    def forward(self, x):
        # x: (batch, H, W, 1) - 渗透率场

        # 添加网格坐标
        grid = self.get_grid(x.shape, x.device)
        x = torch.cat((x, grid), dim=-1)  # (batch, H, W, 3)

        x = self.fc0(x)
        x = x.permute(0, 3, 1, 2)  # (batch, width, H, W)

        # 傅里叶层 + 跳跃连接
        x1 = self.conv0(x)
        x2 = self.w0(x)
        x = x1 + x2
        x = F.gelu(x)

        x1 = self.conv1(x)
        x2 = self.w1(x)
        x = x1 + x2
        x = F.gelu(x)

        x1 = self.conv2(x)
        x2 = self.w2(x)
        x = x1 + x2
        x = F.gelu(x)

        x1 = self.conv3(x)
        x2 = self.w3(x)
        x = x1 + x2

        x = x.permute(0, 2, 3, 1)  # (batch, H, W, width)
        x = self.fc1(x)
        x = F.gelu(x)
        x = self.fc2(x)

        return x

    def get_grid(self, shape, device):
        batchsize, size_x, size_y = shape[0], shape[1], shape[2]
        gridx = torch.linspace(0, 1, size_x, device=device).reshape(1, size_x, 1, 1).repeat(batchsize, 1, size_y, 1)
        gridy = torch.linspace(0, 1, size_y, device=device).reshape(1, 1, size_y, 1).repeat(batchsize, size_x, 1, 1)
        return torch.cat((gridx, gridy), dim=-1)

# 训练
def train_fno(model, train_loader, test_loader, epochs=500):
    optimizer = torch.optim.Adam(model.parameters(), lr=1e-3)
    scheduler = torch.optim.lr_scheduler.StepLR(optimizer, step_size=100, gamma=0.5)

    for epoch in range(epochs):
        model.train()
        train_loss = 0
        for a, u in train_loader:
            optimizer.zero_grad()

            u_pred = model(a)
            loss = F.mse_loss(u_pred, u)

            loss.backward()
            optimizer.step()
            train_loss += loss.item()

        scheduler.step()

        # 测试
        model.eval()
        test_loss = 0
        with torch.no_grad():
            for a, u in test_loader:
                u_pred = model(a)
                test_loss += F.mse_loss(u_pred, u).item()

        if epoch % 10 == 0:
            print(f"Epoch {epoch}, Train Loss: {train_loss/len(train_loader):.6f}, "
                  f"Test Loss: {test_loss/len(test_loader):.6f}")
```

### 3.2 案例二：Burgers方程的神经算子

```python
class FNO1d(nn.Module):
    """1D Fourier神经算子用于Burgers方程"""
    def __init__(self, modes, width):
        super().__init__()
        self.modes = modes
        self.width = width

        self.fc0 = nn.Linear(2, width)  # u0(x), x

        self.conv0 = SpectralConv1d(width, width, modes)
        self.conv1 = SpectralConv1d(width, width, modes)
        self.conv2 = SpectralConv1d(width, width, modes)
        self.conv3 = SpectralConv1d(width, width, modes)

        self.w0 = nn.Conv1d(width, width, 1)
        self.w1 = nn.Conv1d(width, width, 1)
        self.w2 = nn.Conv1d(width, width, 1)
        self.w3 = nn.Conv1d(width, width, 1)

        self.fc1 = nn.Linear(width, 128)
        self.fc2 = nn.Linear(128, 1)

    def forward(self, x):
        # x: (batch, nx, 1) - 初始条件

        grid = self.get_grid(x.shape, x.device)
        x = torch.cat((x, grid), dim=-1)

        x = self.fc0(x)
        x = x.permute(0, 2, 1)

        x1 = self.conv0(x)
        x2 = self.w0(x)
        x = x1 + x2
        x = F.gelu(x)

        x1 = self.conv1(x)
        x2 = self.w1(x)
        x = x1 + x2
        x = F.gelu(x)

        x1 = self.conv2(x)
        x2 = self.w2(x)
        x = x1 + x2
        x = F.gelu(x)

        x1 = self.conv3(x)
        x2 = self.w3(x)
        x = x1 + x2

        x = x.permute(0, 2, 1)
        x = self.fc1(x)
        x = F.gelu(x)
        x = self.fc2(x)

        return x
```

---

## 4. 性能比较与最佳实践

### 4.1 方法比较

| 方法 | 适用问题 | 训练速度 | 推理速度 | 精度 | 数据需求 |
|-----|---------|---------|---------|------|---------|
| PINNs | PDE求解、逆问题 | 慢 | 快 | 中 | 低 |
| 神经ODE | 连续动力学 | 中 | 快 | 高 | 中 |
| 神经SDE | 随机动力学 | 中 | 中 | 高 | 高 |
| FNO | 算子学习 | 快 | 极快 | 高 | 高 |

### 4.2 最佳实践

**PINNs**:

- 使用自适应激活函数
- 平衡各损失项的权重
- 使用因果训练处理时间依赖问题

**神经ODE**:

- 选择合适的ODE求解器
- 使用伴随法节省内存
- 注意梯度消失/爆炸问题

**神经算子**:

- 数据增强提高泛化能力
- 使用超分辨率能力
- 预训练+微调策略

---

*最后更新: 2026年4月 | FormalMath项目*
