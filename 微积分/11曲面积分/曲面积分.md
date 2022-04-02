#  曲面积分概念

【问题】设一曲面 $S$ 的面密度为连续函数 $f(x,y,z)$，求其质量 $M$。

【解决方案】利用极限思想解决的步骤如下：

1. 分割。把曲面 $S$ 分割为 $\Delta S_1,\Delta S_2,\dots,\Delta S_n$ $n$ 个小块，每块的面积也用同样的符号表示。
2. 近似代替。用每块小面积上一点的密度 $f(\xi_i,\eta_i,\zeta_i)$ 代替整个小块的密度，计算质量 $\Delta M_i=f(\xi_i,\eta_i,\zeta_i)\Delta S_i$

3. 求和。$\underset{i}{\sum}\Delta M_i$。
4. 求极限。$M=\underset{\lambda\to0}{\lim} \underset{i}{\sum}\Delta M_i,\quad \lambda=\max\{\Delta S_i\}$。

如果无论如何分割曲面以及无论如何选取 $(\xi_i,\eta_i,\zeta_i)$，上述极限存在且唯一，则称该极限为 $f(x,y,z)$ 在曲面 $S$ 上**对面积的曲面积分**，也称**第一类曲面积分**，记为：
$$
\iint_S f(x,y,z)dS=\lim_{\lambda\to 0}\sum_{i=1}^nf(\xi_i,\eta_i,\zeta_i)\Delta S_i
$$
其中，$dS$ 称为面积元素。

# 曲面面积的计算

如果曲面的方程为 $z=f(x,y)$，则它的面积元素
$$
dS=\sqrt{1+f_x^2+f_y^2} d\sigma
$$
【例题】求抛物面 $z=x^2+y^2, z\le 1$ 的面积。

【解】
$$
S=\iint_SdS=\iint_{x^2+y^2\le 1}\sqrt{1+4x^2+4y^2}dxdy=\int_0^{2\pi}d\theta\int_0^1\rho\sqrt{1+4\rho^2}d\rho=\frac{\pi}{6}(5\sqrt{5}-1)
$$

# 第二类曲面积分

【问题】在电磁场中，通过面积 $S$ 的磁通量 $\varPhi$ 定义为该处磁感应强度的大小 $B$ 与其在 $S$ 法向的投影的乘积，即：$\varPhi=\vec{B}\cdot \vec{S}$。

如果磁通量的大小是与位置有关的函数，即 $\vec{B}(x,y,z)=P(x,y,z)\vec{i}+Q(x,y,z)\vec{j}+R(x,y,z)\vec{k}$，利用极限的思想解决方案如下：

1. 分割。把曲面 $S$ 分割为 $\Delta S_1,\Delta S_2,\dots,\Delta S_n$ 的 $n$ 个小块，每块的面积也用同样的符号表示。
2. 近似代替。用每块小面积上一点的磁感应强度 $\vec{B}(\xi_i,\eta_i,\zeta_i)$ 代替整个小块的磁感应强度，并用单位向量 $\vec{e}_n(\xi_i,\eta_i,\zeta_i)$ 表示这一小块面积的法向，计算磁通量 $\Delta \varPhi_i=\vec{B}(\xi_i,\eta_i,\zeta_i)\cdot\vec{e}_n(\xi_i,\eta_i,\zeta_i)\Delta S_i$

3. 求和。$\underset{i}{\sum}\Delta \varPhi_i$。
4. 求极限。$\varPhi=\underset{\lambda\to0}{\lim} \underset{i}{\sum}\Delta \varPhi_i=\underset{\lambda\to0}{\lim} \underset{i}{\sum}\vec{B}(\xi_i,\eta_i,\zeta_i)\cdot\vec{e}_n(\xi_i,\eta_i,\zeta_i)\Delta S_i,\quad \lambda=\max\{\Delta S_i\}$。

上式其实为 $\vec{B}(x,y,z)\cdot\vec{e}_n(x,y,z)$ 的第一类曲面积分:
$$
\iint_S\vec{B}(x,y,z)\cdot d\vec{S}=\iint_S\vec{B}(x,y,z)\cdot\vec{e}_n(x,y,z)dS
$$
把 $\iint_S\vec{B}(x,y,z)\cdot d\vec{S}$ 称为向量函数 $\vec{B}(x,y,z)$ 的**第二类曲面积分**。

# 对坐标的曲面积分

把 $\vec{e}_n(x,y,z)$ 写成 $\cos\alpha\vec{i}+\cos\beta\vec{j}+\cos\gamma\vec{k}$ 的形式，则：
$$
d\vec{S}=(\cos\alpha\vec{i}+\cos\beta\vec{j}+\cos\gamma\vec{k})dS=dydz\vec{i}+dxdz\vec{j}+dxdy\vec{k}
$$
因此：
$$
\begin{align}
\iint_S\vec{B}(x,y,z)\cdot d\vec{S}
&=\iint_SP(x,y,z)dydz+\iint_SQ(x,y,z)dxdz+\iint_SR(x,y,z)dxdy\\
&=:\iint_SP(x,y,z)dydz+Q(x,y,z)dxdz+R(x,y,z)dxdy
\end{align}
$$
上式称为**对坐标的曲面积分**。

# 对坐标的曲面积分的计算

如果曲面 $S$ 的方程可以表示为 $z=z(z,y),(x,y)\in D_{xy}$，$D(x,y)$ 为 $S$ 在 $xOy$ 上的投影，则：
$$
\iint_SP(x,y,z)dydz+Q(x,y,z)dxdz+R(x,y,z)dxdy\\
=\pm\iint_{D_{xy}}\bigg(P(x,y,z(x,y))(-z_x)+Q(x,y,z(x,y))(-z_y)+R(x,y,z(x,y))\bigg)dxdy
$$
上式关于 $\pm$ 的取法：当曲面法向向上时取 $+$，向下时取 $-$。

【证明】曲面的一个单位法向量为：
$$
\vec{e}_n=\pm\frac{1}{\sqrt{1+(-z_x)^2+(-z_y)^2}}(-z_x,-z_y,1)
$$
而
$$
dS=\sqrt{1+z_x^2+z_y^2}dxdy
$$
代入第二类曲面积分式即可。

【例题】计算 $I=\iint_Sz^2dxdy$，其中 $S$ 为球面 $x^2+y^2+z^2=R^2$ 外侧在第一卦限的部分。

【解】

将 $S$ 向 $xOy$ 面投影计算比较方便。此时 $z=\sqrt{R^2-x^2-y^2}，D_{xy}=\{(x,y)\big|x^2+y^2=R^2,x\ge0,y\ge0\}$

从而：
$$
\begin{align}
I=\iint_Sz^2dxdy
&=\iint_{D_{xy}}(R^2-x^2-y^2)dxdy\\
&=\iint_{D_{xy}}(R^2-\rho^2)\rho d\rho d\theta\\
&=\int_0^\frac{\pi}{2}d\theta\int_0^R(R^2-\rho^2)\rho d\rho\\
&=\frac{\pi}{8}R^4
\end{align}
$$

# 高斯公式

设 $\partial V$ 为 有界闭区域 $V$ 的边界曲面外侧，则：
$$
\oiint_{\partial V}Pdydz+Qdxdz+Rdxdy=\iiint_V\bigg( \frac{\partial P}{\partial x}+\frac{\partial Q}{\partial y}+\frac{\partial R}{\partial z}\bigg)dxdydz
$$


# 斯托克斯公式

$$
\oint_{\partial S} Pdx+Qdy+Rdz=
\iint_S(\frac{\partial R}{\partial y}-\frac{\partial Q}{\partial z})dydz
+(\frac{\partial P}{\partial z}-\frac{\partial R}{\partial x})dzdx
+(\frac{\partial Q}{\partial x}-\frac{\partial P}{\partial y})dxdy
$$

