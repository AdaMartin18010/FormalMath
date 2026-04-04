/**
 * FormalMath 可视化主题配置
 * 提供一致的颜色方案和设计系统
 */

// ============================================
// 类型定义
// ============================================

export interface ColorPalette {
  primary: string;
  primaryLight: string;
  primaryDark: string;
  secondary: string;
  accent: string;
  background: string;
  surface: string;
  surfaceElevated: string;
  text: string;
  textSecondary: string;
  textMuted: string;
  border: string;
  borderLight: string;
  success: string;
  warning: string;
  error: string;
  info: string;
}

export interface NodeTypeColors {
  concept: string;
  theorem: string;
  proof: string;
  example: string;
  application: string;
  mathematician: string;
  axiom: string;
  lemma: string;
  corollary: string;
  definition: string;
  default: string;
}

export interface EdgeTypeColors {
  depends_on: string;
  proves: string;
  uses: string;
  extends: string;
  contradicts: string;
  influences: string;
  references: string;
  default: string;
}

export interface Typography {
  fontFamily: string;
  fontFamilyMono: string;
  fontSize: {
    xs: string;
    sm: string;
    base: string;
    lg: string;
    xl: string;
    '2xl': string;
    '3xl': string;
  };
  fontWeight: {
    normal: number;
    medium: number;
    semibold: number;
    bold: number;
  };
  lineHeight: {
    tight: number;
    normal: number;
    relaxed: number;
  };
}

export interface Spacing {
  xs: string;
  sm: string;
  md: string;
  lg: string;
  xl: string;
  '2xl': string;
  '3xl': string;
}

export interface Shadow {
  sm: string;
  md: string;
  lg: string;
  xl: string;
  inner: string;
  glow: string;
}

export interface BorderRadius {
  none: string;
  sm: string;
  md: string;
  lg: string;
  xl: string;
  full: string;
}

export interface Animation {
  duration: {
    fast: string;
    normal: string;
    slow: string;
  };
  easing: {
    default: string;
    easeIn: string;
    easeOut: string;
    easeInOut: string;
    bounce: string;
  };
}

export interface VisualizationTheme {
  name: string;
  isDark: boolean;
  colors: ColorPalette;
  nodeColors: NodeTypeColors;
  edgeColors: EdgeTypeColors;
  typography: Typography;
  spacing: Spacing;
  shadow: Shadow;
  borderRadius: BorderRadius;
  animation: Animation;
}

// ============================================
// 浅色主题
// ============================================

export const lightTheme: VisualizationTheme = {
  name: 'light',
  isDark: false,
  colors: {
    primary: '#3b82f6',
    primaryLight: '#60a5fa',
    primaryDark: '#2563eb',
    secondary: '#8b5cf6',
    accent: '#f59e0b',
    background: '#f8fafc',
    surface: '#ffffff',
    surfaceElevated: '#f1f5f9',
    text: '#0f172a',
    textSecondary: '#475569',
    textMuted: '#94a3b8',
    border: '#e2e8f0',
    borderLight: '#f1f5f9',
    success: '#10b981',
    warning: '#f59e0b',
    error: '#ef4444',
    info: '#3b82f6',
  },
  nodeColors: {
    concept: '#3b82f6',
    theorem: '#10b981',
    proof: '#8b5cf6',
    example: '#f59e0b',
    application: '#ef4444',
    mathematician: '#ec4899',
    axiom: '#06b6d4',
    lemma: '#6366f1',
    corollary: '#84cc16',
    definition: '#14b8a6',
    default: '#64748b',
  },
  edgeColors: {
    depends_on: '#94a3b8',
    proves: '#10b981',
    uses: '#3b82f6',
    extends: '#8b5cf6',
    contradicts: '#ef4444',
    influences: '#f59e0b',
    references: '#64748b',
    default: '#94a3b8',
  },
  typography: {
    fontFamily: 'Inter, system-ui, -apple-system, sans-serif',
    fontFamilyMono: 'JetBrains Mono, Fira Code, monospace',
    fontSize: {
      xs: '0.75rem',
      sm: '0.875rem',
      base: '1rem',
      lg: '1.125rem',
      xl: '1.25rem',
      '2xl': '1.5rem',
      '3xl': '1.875rem',
    },
    fontWeight: {
      normal: 400,
      medium: 500,
      semibold: 600,
      bold: 700,
    },
    lineHeight: {
      tight: 1.25,
      normal: 1.5,
      relaxed: 1.75,
    },
  },
  spacing: {
    xs: '0.25rem',
    sm: '0.5rem',
    md: '1rem',
    lg: '1.5rem',
    xl: '2rem',
    '2xl': '3rem',
    '3xl': '4rem',
  },
  shadow: {
    sm: '0 1px 2px 0 rgba(0, 0, 0, 0.05)',
    md: '0 4px 6px -1px rgba(0, 0, 0, 0.1), 0 2px 4px -1px rgba(0, 0, 0, 0.06)',
    lg: '0 10px 15px -3px rgba(0, 0, 0, 0.1), 0 4px 6px -2px rgba(0, 0, 0, 0.05)',
    xl: '0 20px 25px -5px rgba(0, 0, 0, 0.1), 0 10px 10px -5px rgba(0, 0, 0, 0.04)',
    inner: 'inset 0 2px 4px 0 rgba(0, 0, 0, 0.06)',
    glow: '0 0 15px rgba(59, 130, 246, 0.5)',
  },
  borderRadius: {
    none: '0',
    sm: '0.25rem',
    md: '0.375rem',
    lg: '0.5rem',
    xl: '0.75rem',
    full: '9999px',
  },
  animation: {
    duration: {
      fast: '150ms',
      normal: '300ms',
      slow: '500ms',
    },
    easing: {
      default: 'cubic-bezier(0.4, 0, 0.2, 1)',
      easeIn: 'cubic-bezier(0.4, 0, 1, 1)',
      easeOut: 'cubic-bezier(0, 0, 0.2, 1)',
      easeInOut: 'cubic-bezier(0.4, 0, 0.2, 1)',
      bounce: 'cubic-bezier(0.68, -0.55, 0.265, 1.55)',
    },
  },
};

// ============================================
// 深色主题
// ============================================

export const darkTheme: VisualizationTheme = {
  name: 'dark',
  isDark: true,
  colors: {
    primary: '#60a5fa',
    primaryLight: '#93c5fd',
    primaryDark: '#3b82f6',
    secondary: '#a78bfa',
    accent: '#fbbf24',
    background: '#0f172a',
    surface: '#1e293b',
    surfaceElevated: '#334155',
    text: '#f8fafc',
    textSecondary: '#cbd5e1',
    textMuted: '#64748b',
    border: '#334155',
    borderLight: '#1e293b',
    success: '#34d399',
    warning: '#fbbf24',
    error: '#f87171',
    info: '#60a5fa',
  },
  nodeColors: {
    concept: '#60a5fa',
    theorem: '#34d399',
    proof: '#a78bfa',
    example: '#fbbf24',
    application: '#f87171',
    mathematician: '#f472b6',
    axiom: '#22d3ee',
    lemma: '#818cf8',
    corollary: '#a3e635',
    definition: '#2dd4bf',
    default: '#94a3b8',
  },
  edgeColors: {
    depends_on: '#475569',
    proves: '#34d399',
    uses: '#60a5fa',
    extends: '#a78bfa',
    contradicts: '#f87171',
    influences: '#fbbf24',
    references: '#64748b',
    default: '#475569',
  },
  typography: lightTheme.typography,
  spacing: lightTheme.spacing,
  shadow: {
    sm: '0 1px 2px 0 rgba(0, 0, 0, 0.3)',
    md: '0 4px 6px -1px rgba(0, 0, 0, 0.4), 0 2px 4px -1px rgba(0, 0, 0, 0.2)',
    lg: '0 10px 15px -3px rgba(0, 0, 0, 0.4), 0 4px 6px -2px rgba(0, 0, 0, 0.2)',
    xl: '0 20px 25px -5px rgba(0, 0, 0, 0.4), 0 10px 10px -5px rgba(0, 0, 0, 0.2)',
    inner: 'inset 0 2px 4px 0 rgba(0, 0, 0, 0.3)',
    glow: '0 0 15px rgba(96, 165, 250, 0.5)',
  },
  borderRadius: lightTheme.borderRadius,
  animation: lightTheme.animation,
};

// ============================================
// 高对比度主题 (无障碍)
// ============================================

export const highContrastTheme: VisualizationTheme = {
  name: 'highContrast',
  isDark: false,
  colors: {
    primary: '#005fcc',
    primaryLight: '#0077ff',
    primaryDark: '#004499',
    secondary: '#6b21a8',
    accent: '#c2410c',
    background: '#ffffff',
    surface: '#ffffff',
    surfaceElevated: '#f3f4f6',
    text: '#000000',
    textSecondary: '#1f2937',
    textMuted: '#4b5563',
    border: '#000000',
    borderLight: '#6b7280',
    success: '#047857',
    warning: '#b45309',
    error: '#dc2626',
    info: '#005fcc',
  },
  nodeColors: {
    concept: '#005fcc',
    theorem: '#047857',
    proof: '#6b21a8',
    example: '#b45309',
    application: '#dc2626',
    mathematician: '#be185d',
    axiom: '#0e7490',
    lemma: '#4338ca',
    corollary: '#3f6212',
    definition: '#0f766e',
    default: '#1f2937',
  },
  edgeColors: {
    depends_on: '#000000',
    proves: '#047857',
    uses: '#005fcc',
    extends: '#6b21a8',
    contradicts: '#dc2626',
    influences: '#b45309',
    references: '#1f2937',
    default: '#000000',
  },
  typography: {
    ...lightTheme.typography,
    fontWeight: {
      normal: 500,
      medium: 600,
      semibold: 700,
      bold: 800,
    },
  },
  spacing: lightTheme.spacing,
  shadow: lightTheme.shadow,
  borderRadius: {
    ...lightTheme.borderRadius,
    sm: '2px',
    md: '4px',
    lg: '6px',
  },
  animation: lightTheme.animation,
};

// ============================================
// 色盲友好主题
// ============================================

export const colorBlindTheme: VisualizationTheme = {
  name: 'colorBlind',
  isDark: false,
  colors: {
    primary: '#0072B2',
    primaryLight: '#56B4E9',
    primaryDark: '#005785',
    secondary: '#CC79A7',
    accent: '#E69F00',
    background: '#F5F5F5',
    surface: '#FFFFFF',
    surfaceElevated: '#EFEFEF',
    text: '#000000',
    textSecondary: '#333333',
    textMuted: '#666666',
    border: '#999999',
    borderLight: '#CCCCCC',
    success: '#009E73',
    warning: '#E69F00',
    error: '#D55E00',
    info: '#0072B2',
  },
  nodeColors: {
    concept: '#0072B2',     // 蓝色
    theorem: '#009E73',     // 蓝绿色
    proof: '#CC79A7',       // 粉色
    example: '#E69F00',     // 橙色
    application: '#D55E00', // 红橙色
    mathematician: '#F0E442', // 黄色
    axiom: '#56B4E9',       // 天蓝色
    lemma: '#882255',       // 深红色
    corollary: '#999999',   // 灰色
    definition: '#117733',  // 绿色
    default: '#666666',
  },
  edgeColors: {
    depends_on: '#999999',
    proves: '#009E73',
    uses: '#0072B2',
    extends: '#CC79A7',
    contradicts: '#D55E00',
    influences: '#E69F00',
    references: '#666666',
    default: '#999999',
  },
  typography: lightTheme.typography,
  spacing: lightTheme.spacing,
  shadow: lightTheme.shadow,
  borderRadius: lightTheme.borderRadius,
  animation: lightTheme.animation,
};

// ============================================
// 主题管理
// ============================================

export const themes = {
  light: lightTheme,
  dark: darkTheme,
  highContrast: highContrastTheme,
  colorBlind: colorBlindTheme,
};

export type ThemeName = keyof typeof themes;

export function getTheme(name: ThemeName): VisualizationTheme {
  return themes[name] || lightTheme;
}

export function applyTheme(theme: VisualizationTheme): void {
  const root = document.documentElement;
  
  // 应用 CSS 变量
  Object.entries(theme.colors).forEach(([key, value]) => {
    root.style.setProperty(`--viz-${key}`, value);
  });

  Object.entries(theme.nodeColors).forEach(([key, value]) => {
    root.style.setProperty(`--viz-node-${key}`, value);
  });

  Object.entries(theme.edgeColors).forEach(([key, value]) => {
    root.style.setProperty(`--viz-edge-${key}`, value);
  });

  // 应用字体
  root.style.setProperty('--viz-font-family', theme.typography.fontFamily);
  root.style.setProperty('--viz-font-mono', theme.typography.fontFamilyMono);

  // 应用深色/浅色模式
  if (theme.isDark) {
    root.classList.add('dark');
  } else {
    root.classList.remove('dark');
  }

  // 应用高对比度
  if (theme.name === 'highContrast') {
    root.classList.add('high-contrast');
  } else {
    root.classList.remove('high-contrast');
  }
}

// ============================================
// 辅助函数
// ============================================

export function getNodeColor(type: string, theme: VisualizationTheme = lightTheme): string {
  return theme.nodeColors[type as keyof NodeTypeColors] || theme.nodeColors.default;
}

export function getEdgeColor(type: string, theme: VisualizationTheme = lightTheme): string {
  return theme.edgeColors[type as keyof EdgeTypeColors] || theme.edgeColors.default;
}

export function adjustOpacity(color: string, opacity: number): string {
  // 处理 hex 颜色
  if (color.startsWith('#')) {
    const r = parseInt(color.slice(1, 3), 16);
    const g = parseInt(color.slice(3, 5), 16);
    const b = parseInt(color.slice(5, 7), 16);
    return `rgba(${r}, ${g}, ${b}, ${opacity})`;
  }
  // 处理 rgb 颜色
  if (color.startsWith('rgb(')) {
    const values = color.slice(4, -1).split(',');
    return `rgba(${values[0].trim()}, ${values[1].trim()}, ${values[2].trim()}, ${opacity})`;
  }
  return color;
}

export function getContrastColor(backgroundColor: string): string {
  // 简单的对比度计算
  const hex = backgroundColor.replace('#', '');
  const r = parseInt(hex.substr(0, 2), 16);
  const g = parseInt(hex.substr(2, 2), 16);
  const b = parseInt(hex.substr(4, 2), 16);
  const brightness = (r * 299 + g * 587 + b * 114) / 1000;
  return brightness > 128 ? '#000000' : '#ffffff';
}

// ============================================
// 导出
// ============================================

export {
  lightTheme as default,
};
