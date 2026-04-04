// ==================== LaTeX公式工具栏组件 ====================
import React, { useState } from 'react';
import {
  Calculator,
  ArrowRight,
  X,
  FunctionSquare,
  Parentheses,
} from 'lucide-react';

// 自定义Sigma图标
const Sigma = () => (
  <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round">
    <path d="M18 6V4H6v2l6 6-6 6v2h12v-2" />
  </svg>
);

// 自定义Delta图标
const Delta = () => (
  <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round">
    <path d="M12 4L4 20h16L12 4z" />
  </svg>
);

// 自定义积分图标
const Integral = ({ className }: { className?: string }) => (
  <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" className={className}>
    <path d="M8 20c0-4 2-12 6-12" />
    <path d="M8 4c0 4 2 12 6 12" />
  </svg>
);

interface LaTeXToolbarProps {
  onInsert: (latex: string) => void;
  className?: string;
}

// LaTeX公式分类
interface FormulaCategory {
  id: string;
  name: string;
  icon: React.ReactNode;
  formulas: FormulaItem[];
}

interface FormulaItem {
  name: string;
  latex: string;
  description?: string;
  preview?: string;
}

const formulaCategories: FormulaCategory[] = [
  {
    id: 'basic',
    name: '基础',
    icon: <Calculator size={16} />,
    formulas: [
      { name: '上标', latex: '^{}', description: 'x^2', preview: 'x²' },
      { name: '下标', latex: '_{}', description: 'x_1', preview: 'x₁' },
      { name: '分数', latex: '\\frac{}{}', description: '\\frac{a}{b}', preview: 'a/b' },
      { name: '根号', latex: '\\sqrt{}', description: '\\sqrt{x}', preview: '√x' },
      { name: 'n次根', latex: '\\sqrt[]{}', description: '\\sqrt[3]{x}', preview: '³√x' },
      { name: '无穷', latex: '\\infty', description: '\\infty', preview: '∞' },
    ],
  },
  {
    id: 'operators',
    name: '运算符',
    icon: <FunctionSquare size={16} />,
    formulas: [
      { name: '加减', latex: '\\pm', description: '\\pm', preview: '±' },
      { name: '乘', latex: '\\times', description: '\\times', preview: '×' },
      { name: '除', latex: '\\div', description: '\\div', preview: '÷' },
      { name: '点乘', latex: '\\cdot', description: '\\cdot', preview: '·' },
      { name: '不等', latex: '\\neq', description: '\\neq', preview: '≠' },
      { name: '小于等于', latex: '\\leq', description: '\\leq', preview: '≤' },
      { name: '大于等于', latex: '\\geq', description: '\\geq', preview: '≥' },
      { name: '约等', latex: '\\approx', description: '\\approx', preview: '≈' },
      { name: '属于', latex: '\\in', description: '\\in', preview: '∈' },
      { name: '包含', latex: '\\subset', description: '\\subset', preview: '⊂' },
    ],
  },
  {
    id: 'calculus',
    name: '微积分',
    icon: <Integral className="w-4 h-4" />,
    formulas: [
      { name: '积分', latex: '\\int', description: '\\int f(x)dx', preview: '∫' },
      { name: '定积分', latex: '\\int_{}^{}', description: '\\int_a^b', preview: '∫ₐᵇ' },
      { name: '二重积分', latex: '\\iint', description: '\\iint', preview: '∬' },
      { name: '三重积分', latex: '\\iiint', description: '\\iiint', preview: '∭' },
      { name: '偏导', latex: '\\frac{\\partial}{\\partial x}', description: '偏导数', preview: '∂/∂x' },
      { name: '极限', latex: '\\lim_{x \\to }', description: '\\lim_{x \\to a}', preview: 'lim' },
      { name: '无穷级数', latex: '\\sum_{n=1}^{\\infty}', description: '求和', preview: 'Σ' },
      { name: '求和', latex: '\\sum_{i=1}^{n}', description: '\\sum_{i=1}^{n}', preview: 'Σ' },
    ],
  },
  {
    id: 'greek',
    name: '希腊字母',
    icon: <Delta />,
    formulas: [
      { name: 'Alpha', latex: '\\alpha', preview: 'α' },
      { name: 'Beta', latex: '\\beta', preview: 'β' },
      { name: 'Gamma', latex: '\\gamma', preview: 'γ' },
      { name: 'Delta', latex: '\\delta', preview: 'δ' },
      { name: 'Delta(大)', latex: '\\Delta', preview: 'Δ' },
      { name: 'Epsilon', latex: '\\epsilon', preview: 'ε' },
      { name: 'Theta', latex: '\\theta', preview: 'θ' },
      { name: 'Lambda', latex: '\\lambda', preview: 'λ' },
      { name: 'Mu', latex: '\\mu', preview: 'μ' },
      { name: 'Pi', latex: '\\pi', preview: 'π' },
      { name: 'Pi(大)', latex: '\\Pi', preview: 'Π' },
      { name: 'Sigma', latex: '\\sigma', preview: 'σ' },
      { name: 'Sigma(大)', latex: '\\Sigma', preview: 'Σ' },
      { name: 'Phi', latex: '\\phi', preview: 'φ' },
      { name: 'Phi(大)', latex: '\\Phi', preview: 'Φ' },
      { name: 'Omega', latex: '\\omega', preview: 'ω' },
    ],
  },
  {
    id: 'arrows',
    name: '箭头',
    icon: <ArrowRight size={16} />,
    formulas: [
      { name: '左', latex: '\\leftarrow', preview: '←' },
      { name: '右', latex: '\\rightarrow', preview: '→' },
      { name: '左右', latex: '\\leftrightarrow', preview: '↔' },
      { name: '长右', latex: '\\longrightarrow', preview: '⟶' },
      { name: '映射', latex: '\\mapsto', preview: '↦' },
      { name: '双向', latex: '\\Leftrightarrow', preview: '⇔' },
      { name: '推出', latex: '\\Rightarrow', preview: '⇒' },
      { name: '上', latex: '\\uparrow', preview: '↑' },
      { name: '下', latex: '\\downarrow', preview: '↓' },
    ],
  },
  {
    id: 'brackets',
    name: '括号',
    icon: <Parentheses size={16} />,
    formulas: [
      { name: '圆括号', latex: '\\left(  \\right)', preview: '( )' },
      { name: '方括号', latex: '\\left[  \\right]', preview: '[ ]' },
      { name: '花括号', latex: '\\left\\{  \\right\\}', preview: '{ }' },
      { name: '尖括号', latex: '\\left\\langle  \\right\\rangle', preview: '⟨ ⟩' },
      { name: '竖线', latex: '\\left|  \\right|', preview: '| |' },
      { name: '双竖线', latex: '\\left\\|  \\right\\|', preview: '‖ ‖' },
      { name: '上取整', latex: '\\lceil  \\rceil', preview: '⌈ ⌉' },
      { name: '下取整', latex: '\\lfloor  \\rfloor', preview: '⌊ ⌋' },
    ],
  },
  {
    id: 'advanced',
    name: '高级',
    icon: <Sigma />,
    formulas: [
      { name: '矩阵', latex: '\\begin{pmatrix} a & b \\\\ c & d \\end{pmatrix}', description: '2x2矩阵' },
      { name: '分段', latex: '\\begin{cases} x & x>0 \\\\ -x & x<0 \\end{cases}', description: '分段函数' },
      { name: '对齐', latex: '\\begin{aligned} & x \\\\ = & y \\end{aligned}', description: '对齐公式' },
      { name: '向量', latex: '\\vec{a}', description: '\\vec{a}', preview: 'a⃗' },
      { name: '梯度', latex: '\\nabla', description: '\\nabla', preview: '∇' },
      { name: '无穷积', latex: '\\prod_{i=1}^{n}', description: '连乘', preview: '∏' },
      { name: '偏导符号', latex: '\\partial', description: '\\partial', preview: '∂' },
      { name: '自然对数', latex: '\\ln', description: '\\ln', preview: 'ln' },
      { name: '指数', latex: '\\exp', description: '\\exp', preview: 'exp' },
      { name: '正弦', latex: '\\sin', description: '\\sin', preview: 'sin' },
      { name: '余弦', latex: '\\cos', description: '\\cos', preview: 'cos' },
    ],
  },
];

// 快捷公式
const quickFormulas = [
  { name: '二次公式', latex: 'x = \\frac{-b \\pm \\sqrt{b^2-4ac}}{2a}' },
  { name: '导数定义', latex: "f'(x) = \\lim_{h \\to 0} \\frac{f(x+h)-f(x)}{h}" },
  { name: '积分公式', latex: '\\int_{a}^{b} f(x) \\, dx = F(b) - F(a)' },
  { name: '欧拉公式', latex: 'e^{i\\pi} + 1 = 0' },
  { name: '泰勒展开', latex: 'f(x) = \\sum_{n=0}^{\\infty} \\frac{f^{(n)}(a)}{n!}(x-a)^n' },
  { name: '柯西定理', latex: '\\oint_C f(z) \\, dz = 0' },
];

export const LaTeXToolbar: React.FC<LaTeXToolbarProps> = ({ onInsert, className = '' }) => {
  const [isOpen, setIsOpen] = useState(false);
  const [activeCategory, setActiveCategory] = useState<string>('basic');
  const [showQuickFormulas, setShowQuickFormulas] = useState(false);

  const activeFormulas = formulaCategories.find((c) => c.id === activeCategory)?.formulas || [];

  const handleInsert = (latex: string) => {
    onInsert(latex);
  };

  if (!isOpen) {
    return (
      <button
        onClick={() => setIsOpen(true)}
        className="
          flex items-center px-3 py-1.5
          bg-purple-100 text-purple-700 rounded-lg
          hover:bg-purple-200 transition-colors text-sm
        "
      >
        <Calculator className="w-4 h-4 mr-1.5" />
        LaTeX公式
      </button>
    );
  }

  return (
    <div className={`bg-white rounded-xl shadow-lg border border-gray-200 ${className}`}>
      {/* 头部 */}
      <div className="flex items-center justify-between px-4 py-3 border-b border-gray-200">
        <div className="flex items-center">
          <Calculator className="w-5 h-5 text-purple-500 mr-2" />
          <h3 className="font-semibold text-gray-800">LaTeX公式助手</h3>
        </div>
        <div className="flex items-center space-x-2">
          <button
            onClick={() => setShowQuickFormulas(!showQuickFormulas)}
            className="
              text-sm text-purple-600 hover:text-purple-700
              px-2 py-1 rounded hover:bg-purple-50
            "
          >
            常用公式
          </button>
          <button
            onClick={() => setIsOpen(false)}
            className="p-1 text-gray-400 hover:text-gray-600 hover:bg-gray-100 rounded"
          >
            <X size={16} />
          </button>
        </div>
      </div>

      {/* 常用公式快捷栏 */}
      {showQuickFormulas && (
        <div className="px-4 py-3 bg-purple-50 border-b border-purple-100">
          <h4 className="text-xs font-medium text-purple-700 mb-2">常用公式</h4>
          <div className="flex flex-wrap gap-2">
            {quickFormulas.map((formula, index) => (
              <button
                key={index}
                onClick={() => handleInsert(`$${formula.latex}$`)}
                className="
                  px-3 py-1.5 bg-white text-purple-700 text-sm
                  border border-purple-200 rounded-lg
                  hover:bg-purple-100 transition-colors
                "
                title={formula.latex}
              >
                {formula.name}
              </button>
            ))}
          </div>
        </div>
      )}

      {/* 分类标签 */}
      <div className="flex border-b border-gray-200 overflow-x-auto">
        {formulaCategories.map((category) => (
          <button
            key={category.id}
            onClick={() => setActiveCategory(category.id)}
            className={`
              flex items-center px-4 py-3 text-sm whitespace-nowrap
              border-b-2 transition-colors
              ${
                activeCategory === category.id
                  ? 'border-purple-500 text-purple-600 bg-purple-50'
                  : 'border-transparent text-gray-600 hover:text-gray-800 hover:bg-gray-50'
              }
            `}
          >
            <span className="mr-1.5">{category.icon}</span>
            {category.name}
          </button>
        ))}
      </div>

      {/* 公式网格 */}
      <div className="p-4 max-h-64 overflow-y-auto">
        <div className="grid grid-cols-4 gap-2">
          {activeFormulas.map((formula, index) => (
            <button
              key={index}
              onClick={() => handleInsert(formula.latex)}
              className="
                p-3 rounded-lg border border-gray-200
                hover:border-purple-300 hover:bg-purple-50
                transition-all text-center group
              "
              title={formula.description || formula.latex}
            >
              {formula.preview ? (
                <span className="text-lg">{formula.preview}</span>
              ) : (
                <span className="text-xs text-gray-500 font-mono truncate block">
                  {formula.latex.slice(0, 20)}...
                </span>
              )}
              <span className="text-xs text-gray-500 block mt-1 group-hover:text-purple-600">
                {formula.name}
              </span>
            </button>
          ))}
        </div>
      </div>

      {/* 底部提示 */}
      <div className="px-4 py-2 bg-gray-50 border-t border-gray-200 text-xs text-gray-500">
        点击公式即可插入，使用 {} 表示需要填写的内容
      </div>
    </div>
  );
};

export default LaTeXToolbar;
