# 粗糙分析：应用领域详解

> 粗糙路径理论在金融数学、机器学习和物理中的具体应用

---

## 1. 金融数学应用：粗糙波动率模型

### 1.1 波动率的粗糙性

**实证发现** (Gatheral et al., 2018):

对数波动率的增量表现出**粗糙**行为：
$$\text{Corr}(\log \sigma_t, \log \sigma_{t+\Delta}) \approx 1 - C|\Delta|^{2H}$$
其中 $H \approx 0.1 \ll 1/2$。

这意味着：

- 波动率不是半鞅
- 传统随机波动率模型不适用
- 需要粗糙路径理论

### 1.2 粗糙Heston模型

**模型定义**:

标的资产价格 $S_t$ 满足：
$$dS_t = S_t \sqrt{V_t} dW_t$$
其中方差过程 $V_t$ 是**粗糙**的：
$$V_t = V_0 + \frac{\nu}{\Gamma(H + 1/2)} \int_0^t (t-s)^{H-1/2} (\theta - V_s) ds + \text{(噪声项)}$$

对于 $H < 1/2$，这给出分数布朗运动类型的粗糙性。

**粗糙路径表述**:

使用粗糙微分方程 (RDE)：
$$d\mathbf{S}_t = \mathbf{S}_t \otimes \sqrt{V_t} d\mathbf{W}_t$$
其中 $\mathbf{W}$ 是粗糙路径提升。

### 1.3 粗糙Bergomi模型

**Bergomi模型** (2015) 的粗糙版本：

$$V_t = \xi_0(t) \cdot \exp\left(\nu \cdot Y_t - \frac{\nu^2}{2} t^{2H}\right)$$

其中 $Y_t$ 是粗糙高斯过程，协方差：
$$\text{Cov}(Y_t, Y_s) = \frac{1}{2}\left(t^{2H} + s^{2H} - |t-s|^{2H}\right)$$

**特点**:

- 自动捕捉波动率微笑的粗糙行为
- 仅需少量参数 ($H, \nu, \rho$)
- 与粗糙Heston模型有精确关系

### 1.4 期权定价的具体计算

**特征函数方法**:

对于粗糙Heston模型，对数价格的**特征函数**有显式公式：

$$\phi_T(u) = \mathbb{E}[e^{iu \log S_T}] = \exp(g_1(u) + V_0 \cdot g_2(u))$$

其中 $g_1, g_2$ 通过分数Riccati方程定义：
$$D^\alpha g_2(u) = f(u, g_2(u)), \quad g_2(0) = 0$$

**计算步骤**:

```python
# 伪代码：粗糙Heston的特征函数计算
def rough_heston_characteristic(u, T, H, V0, theta, nu, rho):
    """
    计算粗糙Heston模型的特征函数

    参数:
    u: 频率参数
    T: 到期时间
    H: Hurst参数 (粗糙性)
    V0: 初始方差
    theta: 长期方差
    nu: vol-of-vol
    rho: 相关系数
    """
    # 1. 求解分数Riccati方程
    g2 = solve_fractional_riccati(u, T, H, theta, nu, rho)

    # 2. 计算g1
    g1 = compute_g1_integral(g2, T, H)

    # 3. 返回特征函数
    return np.exp(g1 + V0 * g2)
```

**期权定价公式** (Lewis方法):

$$C(K, T) = S_0 - \frac{\sqrt{S_0 K}}{\pi} \int_0^\infty \text{Re}\left(\frac{e^{(iu-1/2)\log(S_0/K)} \phi_T(u-1/2)}{u^2 + 1/4}\right) du$$

### 1.5 实际市场数据拟合

**参数校准**:

| 参数 | 物理意义 | 典型值 | 校准方法 |
|-----|---------|--------|---------|
| $H$ | 粗糙程度 | 0.05-0.15 | ATM skew |
| $\nu$ | vol-of-vol | 1.0-3.0 | 微笑曲率 |
| $\rho$ | 杠杆效应 | -0.8--0.5 | 倾斜方向 |
| $V_0$ | 初始方差 | 0.02-0.05 | ATM水平 |

**模型性能**:

- 粗糙模型对SPX期权的拟合误差 < 1%
- 传统SV模型误差通常为 2-5%
- 关键：自动捕捉期限结构

---

## 2. 机器学习中的签名方法

### 2.1 签名的特征提取能力

**签名变换**:

对于路径 $X: [0, T] \to \mathbb{R}^d$，**签名** $S(X)$ 是迭代积分序列：
$$S(X) = (1, S^1(X), S^2(X), \ldots)$$
其中：
$$S^k(X) = \left(\int_{0<t_1<\cdots<t_k<T} dX^{i_1}_{t_1} \cdots dX^{i_k}_{t_k}\right)_{i_1, \ldots, i_k \in \{1, \ldots, d\}}$$

**特征维度**: 截断到深度 $N$ 的签名维度为 $\frac{d^{N+1}-1}{d-1}$。

### 2.2 时间序列分类

**应用流程**:

```
原始时间序列 → 路径提升 → 签名计算 → 特征向量 → 机器学习模型
```

**具体例子：手写数字识别**:

将MNIST的像素序列转换为路径：

- 按行或按列扫描
- 归一化并插值
- 计算签名到深度 3-5
- 使用SVM或随机森林分类

**代码示例** (Python):

```python
import iisignature
from sklearn.ensemble import RandomForestClassifier

def signature_features(paths, depth=3):
    """
    计算路径批次的签名特征

    参数:
    paths: 形状为 (n_samples, n_timesteps, d) 的路径数组
    depth: 签名截断深度

    返回:
    特征矩阵 (n_samples, n_features)
    """
    d = paths.shape[2]
    features = []

    for path in paths:
        # 计算签名 (去除首项1)
        sig = iisignature.sig(path, depth)[1:]
        features.append(sig)

    return np.array(features)

# 训练分类器
X_sig = signature_features(training_paths, depth=4)
clf = RandomForestClassifier(n_estimators=100)
clf.fit(X_sig, y_train)

# 预测
X_test_sig = signature_features(test_paths, depth=4)
predictions = clf.predict(X_test_sig)
```

### 2.3 金融时间序列预测

**应用：股价趋势预测**:

1. **数据预处理**:
   - 提取OHLCV时间序列
   - 构建多维路径：价格、成交量、波动率

2. **签名特征工程**:

   ```python
   def financial_signature_features(df, window=20, depth=3):
       """
       从金融数据框计算签名特征
       """
       features = []

       for i in range(window, len(df)):
           # 提取窗口
           window_data = df.iloc[i-window:i]

           # 构建路径
           path = np.column_stack([
               window_data['close'].values,
               window_data['volume'].values,
               window_data['volatility'].values
           ])

           # 计算签名
           sig = iisignature.sig(path, depth)
           features.append(sig)

       return np.array(features)
   ```

3. **模型训练**:
   - 使用LSTM或Transformer
   - 签名作为静态特征输入
   - 原始序列作为动态输入

### 2.4 深度签名方法

**深度签名网络** (DeepSignature):

```
输入路径 X
    ↓
神经网络编码器 f_θ
    ↓
潜在路径 Z = f_θ(X)
    ↓
签名层 S(Z)
    ↓
预测头
    ↓
输出
```

**PyTorch实现**:

```python
import torch
import torch.nn as nn
import signatory

class DeepSignatureNet(nn.Module):
    def __init__(self, input_dim, hidden_dim, signature_depth, output_dim):
        super().__init__()

        # 路径编码器
        self.encoder = nn.Sequential(
            nn.Linear(input_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, hidden_dim),
            nn.ReLU()
        )

        # 签名深度
        self.signature_depth = signature_depth

        # 计算签名维度
        self.signature_dim = signatory.signature_channels(
            channels=hidden_dim,
            depth=signature_depth
        )

        # 预测头
        self.predictor = nn.Sequential(
            nn.Linear(self.signature_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, output_dim)
        )

    def forward(self, path):
        # path: (batch, timesteps, input_dim)

        # 编码
        encoded = self.encoder(path)  # (batch, timesteps, hidden_dim)

        # 计算签名
        signature = signatory.signature(
            encoded,
            depth=self.signature_depth
        )  # (batch, signature_dim)

        # 预测
        output = self.predictor(signature)

        return output
```

### 2.5 签名核方法

**签名核** (Signature Kernel):

对于两条路径 $X, Y$，定义内积：
$$K(X, Y) = \langle S(X), S(Y) \rangle$$

**高效计算**:

使用PDE方法，签名核可以在 $O(n \cdot m)$ 时间计算：

```python
import signatory

def signature_kernel(X, Y, static_kernel=None):
    """
    计算两条路径的签名核

    参数:
    X, Y: 路径，形状为 (timesteps, dim)
    static_kernel: 静态核函数（默认线性）

    返回:
    核值 K(X, Y)
    """
    return signatory.signature_kernel(X, Y, static_kernel)

# 批处理版本
K_matrix = signatory.signature_kernel_batch(paths_list)
```

**支持向量机应用**:

```python
from sklearn.svm import SVC

# 使用预计算的签名核矩阵
svm = SVC(kernel='precomputed')
svm.fit(K_train, y_train)
predictions = svm.predict(K_test)
```

---

## 3. 具体计算示例

### 3.1 签名的数值计算

**算法：Chen迭代积分**:

对于离散路径 $X_0, X_1, \ldots, X_n$，签名的迭代计算：

```python
def compute_signature_discrete(path, depth):
    """
    离散路径的签名计算

    参数:
    path: 形状为 (n_points, d) 的数组
    depth: 截断深度

    返回:
    签名向量
    """
    n, d = path.shape

    # 计算增量
    increments = np.diff(path, axis=0)  # (n-1, d)

    # 初始化
    signature = [np.array([1.0])]  # 0阶项
    current_level = np.ones(n-1)  # 用于计算的累积

    for k in range(1, depth + 1):
        next_level = []
        # 计算k阶迭代积分
        for indices in product(range(d), repeat=k):
            integral = 0.0
            for t in range(n-1):
                product = 1.0
                for i, idx in enumerate(indices):
                    # 简化的迭代积分计算
                    product *= increments[t, idx]
                integral += product
            next_level.append(integral)

        signature.append(np.array(next_level))

    return np.concatenate(signature)
```

**优化库推荐**:

| 库名 | 语言 | 特点 | 适用场景 |
|-----|------|------|---------|
| iisignature | Python/C++ | 快速，准确 | 生产环境 |
| signatory | Python/PyTorch | GPU支持，可微分 | 深度学习 |
| esig | C++/Python | 内存高效 | 大规模数据 |
| RoughPy | Python/C++ | 完整粗糙路径支持 | 研究 |

### 3.2 粗糙微分方程的数值求解

**Euler方案** (对于p-粗糙路径，$p < 3$):

```python
def rough_euler_step(y, rough_path, drift, diffusion, dt):
    """
    粗糙Euler单步

    参数:
    y: 当前状态
    rough_path: 粗糙路径 (包含1阶和2阶增量)
    drift: 漂移函数
    diffusion: 扩散函数
    dt: 时间步长
    """
    # 提取粗糙路径分量
    X1 = rough_path.first_level  # 1阶增量
    X2 = rough_path.second_level  # 2阶增量（Levy面积）

    # Euler-Maruyama类型更新
    dy = drift(y) * dt + diffusion(y) @ X1

    # 粗糙修正项（需要扩散的导数）
    if hasattr(rough_path, 'second_level'):
        D_diffusion = jacobian(diffusion, y)
        correction = 0.5 * np.einsum('ijk,jk->i', D_diffusion, X2)
        dy += correction

    return y + dy
```

**Davies展开** (高阶近似):

```python
def davies_scheme(y0, rough_path, vector_fields, N=3):
    """
    使用Davies展开求解RDE

    参数:
    y0: 初始条件
    rough_path: 驱动粗糙路径
    vector_fields: 向量场列表 [V_1, ..., V_d]
    N: 展开阶数
    """
    y = y0

    for segment in rough_path.segments:
        # 计算Lie括号展开
        increment = y * 0

        # 一阶项
        for i, V in enumerate(vector_fields):
            increment += V(y) * segment.signature[(i,)]

        # 二阶Lie括号项
        if N >= 2:
            for i, V in enumerate(vector_fields):
                for j, W in enumerate(vector_fields):
                    lie_bracket = lambda y: jacobian(V, y) @ W(y) - jacobian(W, y) @ V(y)
                    increment += 0.5 * lie_bracket(y) * segment.signature[(i, j)]

        y = y + increment

    return y
```

### 3.3 金融衍生品定价实例

**完整示例：粗糙Heston下的欧式看涨期权**:

```python
import numpy as np
from scipy.integrate import quad
from scipy.special import gamma

def rough_heston_cf(u, T, params):
    """
    粗糙Heston的特征函数

    参数:
    params = {H, lambda, theta, nu, V0, rho}
    """
    H = params['H']
    lambda_ = params['lambda']
    theta = params['theta']
    nu = params['nu']
    V0 = params['V0']
    rho = params['rho']

    # 分数Riccati方程的解 (使用近似)
    # 这里使用ADM分解或数值方法

    # 简化：使用已知的级数展开
    alpha = H + 0.5

    # 特征函数的对数
    # ... (复杂计算)

    return np.exp(cf_log)

def european_call_rough_heston(S0, K, T, params):
    """
    粗糙Heston模型下的欧式看涨期权价格

    使用Carr-Madan公式
    """
    k = np.log(K / S0)

    # 积分函数
    def integrand(u):
        cf = rough_heston_cf(u - 0.5j, T, params)
        return np.real(np.exp(-1j * u * k) * cf / (u**2 + 0.25))

    # 数值积分
    integral, _ = quad(integrand, 0, np.inf, limit=100)

    # 期权价格
    price = S0 - np.sqrt(S0 * K) * integral / np.pi

    return max(price, 0)  # 无套利约束

# 参数设置
params = {
    'H': 0.05,        # 粗糙性
    'lambda': 1.0,    # 均值回归速度
    'theta': 0.04,    # 长期方差
    'nu': 0.3,        # vol-of-vol
    'V0': 0.04,       # 初始方差
    'rho': -0.7       # 相关系数
}

# 定价
S0, K, T = 100, 100, 1.0
price = european_call_rough_heston(S0, K, T, params)
print(f"欧式看涨期权价格: {price:.4f}")
```

---

## 4. 其他应用领域

### 4.1 医疗健康

**心电图 (ECG) 分析**:

- 将ECG信号转换为路径
- 签名特征捕捉心律模式
- 用于心律失常检测

**代码片段**:

```python
def ecg_signature_features(ecg_signal, sampling_rate=250):
    # 预处理
    filtered = bandpass_filter(ecg_signal, 0.5, 40, sampling_rate)

    # 检测R峰
    r_peaks = detect_r_peaks(filtered, sampling_rate)

    # 构建心跳间期的路径
    rr_intervals = np.diff(r_peaks) / sampling_rate
    path = np.column_stack([np.arange(len(rr_intervals)), rr_intervals])

    # 计算签名
    return iisignature.sig(path, depth=3)
```

### 4.2 自然语言处理

**文本作为路径**:

- 词嵌入序列 → 高维路径
- 签名捕捉语义结构
- 用于文本分类和情感分析

### 4.3 强化学习

**策略梯度中的签名**:

- 状态历史编码为签名
- 处理部分可观察性
- 捕捉长期依赖

---

## 参考文献

1. Gatheral, J., Jaisson, T., Rosenbaum, M. (2018). "Volatility is rough"
2. Bayer, C., Friz, P., Gatheral, J. (2016). "Pricing under rough volatility"
3. Lyons, T. (2014). "Rough paths, Signatures and the modelling of functions on streams"
4. Chevyrev, I., Kormilitzin, A. (2016). "A Primer on the Signature Method in Machine Learning"
5. Lemercier et al. (2021). "SigGPDE: Scaling Sparse Gaussian Processes on Sequential Data"
