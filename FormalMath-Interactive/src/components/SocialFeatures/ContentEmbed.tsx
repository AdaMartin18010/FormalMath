import React, { useState, useCallback, useRef, useEffect } from 'react';
import { 
  Code2, 
  Copy, 
  Check, 
  ExternalLink,
  Settings,
  Maximize2,
  Minimize2,
  RefreshCw,
  Download,
  Share2
} from 'lucide-react';

export type EmbedSize = 'small' | 'medium' | 'large' | 'custom' | 'responsive';
export type EmbedTheme = 'light' | 'dark' | 'auto';

export interface EmbedConfig {
  width: number | string;
  height: number | string;
  size: EmbedSize;
  theme: EmbedTheme;
  showHeader: boolean;
  showFooter: boolean;
  allowFullscreen: boolean;
  allowInteraction: boolean;
  autoResize: boolean;
  hideScrollbars: boolean;
  borderRadius: number;
  border: boolean;
  shadow: boolean;
  lang?: string;
}

export interface ContentEmbedProps {
  url: string;
  title: string;
  description?: string;
  thumbnail?: string;
  config?: Partial<EmbedConfig>;
  onConfigChange?: (config: EmbedConfig) => void;
  className?: string;
}

const defaultConfig: EmbedConfig = {
  width: '100%',
  height: 600,
  size: 'responsive',
  theme: 'auto',
  showHeader: true,
  showFooter: false,
  allowFullscreen: true,
  allowInteraction: true,
  autoResize: false,
  hideScrollbars: false,
  borderRadius: 8,
  border: true,
  shadow: true,
};

const sizePresets: Record<EmbedSize, { width: string; height: number }> = {
  small: { width: '100%', height: 300 },
  medium: { width: '100%', height: 450 },
  large: { width: '100%', height: 600 },
  custom: { width: '100%', height: 600 },
  responsive: { width: '100%', height: 600 },
};

export const ContentEmbed: React.FC<ContentEmbedProps> = ({
  url,
  title,
  description,
  thumbnail,
  config: initialConfig,
  onConfigChange,
  className = '',
}) => {
  const [config, setConfig] = useState<EmbedConfig>({ ...defaultConfig, ...initialConfig });
  const [showCode, setShowCode] = useState(false);
  const [copied, setCopied] = useState(false);
  const [fullscreen, setFullscreen] = useState(false);
  const [loading, setLoading] = useState(true);
  const iframeRef = useRef<HTMLIFrameElement>(null);

  const updateConfig = useCallback((updates: Partial<EmbedConfig>) => {
    const newConfig = { ...config, ...updates };
    setConfig(newConfig);
    onConfigChange?.(newConfig);
  }, [config, onConfigChange]);

  const handleSizeChange = (size: EmbedSize) => {
    const preset = sizePresets[size];
    updateConfig({ 
      size, 
      width: preset.width, 
      height: preset.height 
    });
  };

  const generateEmbedCode = (): string => {
    const params = new URLSearchParams();
    
    if (config.theme !== 'auto') params.set('theme', config.theme);
    if (!config.showHeader) params.set('header', '0');
    if (!config.showFooter) params.set('footer', '0');
    if (config.lang) params.set('lang', config.lang);
    if (config.allowInteraction) params.set('interactive', '1');

    const embedUrl = `${url}/embed?${params.toString()}`;
    
    const styles: string[] = [];
    if (config.borderRadius > 0) styles.push(`border-radius: ${config.borderRadius}px;`);
    if (config.border) styles.push('border: 1px solid #e5e7eb;');
    if (config.shadow) styles.push('box-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.1);');
    if (config.hideScrollbars) styles.push('overflow: hidden;');

    const styleString = styles.length > 0 ? ` style="${styles.join(' ')}"` : '';

    let code = '';

    // iframe embed
    code += `<!-- ${title} 嵌入代码 -->\n`;
    code += `<iframe\n`;
    code += `  src="${embedUrl}"\n`;
    code += `  width="${config.width}"\n`;
    code += `  height="${config.height}"\n`;
    code += `  title="${title}"\n`;
    code += `  frameborder="0"\n`;
    code += `  allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture"\n`;
    if (config.allowFullscreen) code += `  allowfullscreen\n`;
    code += `  loading="lazy"\n`;
    code += `  referrerpolicy="no-referrer-when-downgrade"\n`;
    code += `${styleString}\n`;
    code += `></iframe>`;

    // Responsive wrapper
    if (config.size === 'responsive') {
      code = `<!-- 响应式容器 -->\n`;
      code += `<div class="formalmath-embed-container" style="position: relative; padding-bottom: 56.25%; height: 0; overflow: hidden; max-width: 100%;">\n`;
      code += `  <iframe\n`;
      code += `    src="${embedUrl}"\n`;
      code += `    style="position: absolute; top: 0; left: 0; width: 100%; height: 100%; border: 0;"\n`;
      code += `    title="${title}"\n`;
      code += `    allowfullscreen\n`;
      code += `    loading="lazy"\n`;
      code += `  ></iframe>\n`;
      code += `</div>`;
    }

    // JavaScript API option
    code += `\n\n<!-- 或者使用 JavaScript API -->\n`;
    code += `<div id="formalmath-embed"></div>\n`;
    code += `<script src="${window.location.origin}/embed.js"></script>\n`;
    code += `<script>\n`;
    code += `  FormalMathEmbed.init({\n`;
    code += `    container: '#formalmath-embed',\n`;
    code += `    url: '${url}',\n`;
    code += `    width: '${config.width}',\n`;
    code += `    height: ${config.height},\n`;
    code += `    theme: '${config.theme}',\n`;
    code += `    header: ${config.showHeader},\n`;
    code += `    footer: ${config.showFooter}\n`;
    code += `  });\n`;
    code += `</script>`;

    return code;
  };

  const generateOEmbedUrl = (): string => {
    return `${window.location.origin}/oembed?url=${encodeURIComponent(url)}&format=json`;
  };

  const handleCopy = useCallback(async () => {
    try {
      await navigator.clipboard.writeText(generateEmbedCode());
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    } catch (err) {
      console.error('Failed to copy:', err);
    }
  }, [config, url, title]);

  const handleRefresh = () => {
    if (iframeRef.current) {
      iframeRef.current.src = iframeRef.current.src;
    }
  };

  const toggleFullscreen = () => {
    setFullscreen(!fullscreen);
  };

  // Auto-resize handler
  useEffect(() => {
    if (!config.autoResize || !iframeRef.current) return;

    const handleMessage = (event: MessageEvent) => {
      if (event.origin !== window.location.origin) return;
      if (event.data.type === 'embed:resize') {
        const { height } = event.data;
        if (iframeRef.current && height) {
          iframeRef.current.style.height = `${height}px`;
        }
      }
    };

    window.addEventListener('message', handleMessage);
    return () => window.removeEventListener('message', handleMessage);
  }, [config.autoResize]);

  const params = new URLSearchParams();
  if (config.theme !== 'auto') params.set('theme', config.theme);
  if (!config.showHeader) params.set('header', '0');
  if (!config.showFooter) params.set('footer', '0');
  if (config.lang) params.set('lang', config.lang);

  const embedUrl = `${url}/embed?${params.toString()}`;

  return (
    <div className={`bg-white rounded-lg shadow-lg overflow-hidden ${className}`}>
      {/* Header */}
      <div className="flex items-center justify-between px-4 py-3 bg-gray-50 border-b border-gray-200">
        <div className="flex items-center gap-3">
          {thumbnail && (
            <img 
              src={thumbnail} 
              alt={title} 
              className="w-10 h-10 rounded object-cover"
            />
          )}
          <div>
            <h3 className="font-semibold text-gray-800">{title}</h3>
            {description && (
              <p className="text-sm text-gray-500">{description}</p>
            )}
          </div>
        </div>
        <div className="flex items-center gap-2">
          <button
            onClick={handleRefresh}
            className="p-2 text-gray-500 hover:text-gray-700 hover:bg-gray-200 rounded-lg transition-colors"
            title="刷新"
          >
            <RefreshCw size={18} />
          </button>
          <button
            onClick={toggleFullscreen}
            className="p-2 text-gray-500 hover:text-gray-700 hover:bg-gray-200 rounded-lg transition-colors"
            title={fullscreen ? '退出全屏' : '全屏'}
          >
            {fullscreen ? <Minimize2 size={18} /> : <Maximize2 size={18} />}
          </button>
          <button
            onClick={() => setShowCode(!showCode)}
            className={`p-2 rounded-lg transition-colors ${
              showCode 
                ? 'text-blue-600 bg-blue-100' 
                : 'text-gray-500 hover:text-gray-700 hover:bg-gray-200'
            }`}
            title="嵌入代码"
          >
            <Code2 size={18} />
          </button>
        </div>
      </div>

      {/* Preview */}
      <div className={`relative ${fullscreen ? 'fixed inset-0 z-50 bg-black' : ''}`}>
        {loading && (
          <div className="absolute inset-0 flex items-center justify-center bg-gray-100">
            <div className="flex items-center gap-2 text-gray-500">
              <RefreshCw size={20} className="animate-spin" />
              <span>加载中...</span>
            </div>
          </div>
        )}
        <iframe
          ref={iframeRef}
          src={embedUrl}
          title={title}
          width={fullscreen ? '100%' : config.width}
          height={fullscreen ? '100vh' : config.height}
          frameBorder="0"
          allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture"
          allowFullScreen={config.allowFullscreen}
          onLoad={() => setLoading(false)}
          className={`
            transition-all duration-300
            ${config.hideScrollbars ? 'overflow-hidden' : ''}
          `}
          style={{
            borderRadius: fullscreen ? 0 : config.borderRadius,
            border: config.border ? '1px solid #e5e7eb' : 'none',
            boxShadow: config.shadow && !fullscreen ? '0 4px 6px -1px rgba(0, 0, 0, 0.1)' : 'none',
          }}
        />
        {fullscreen && (
          <button
            onClick={toggleFullscreen}
            className="absolute top-4 right-4 p-2 bg-white/90 rounded-lg shadow-lg"
          >
            <Minimize2 size={20} />
          </button>
        )}
      </div>

      {/* Embed Code Panel */}
      {showCode && (
        <div className="border-t border-gray-200 bg-gray-50 p-4">
          {/* Configuration */}
          <div className="mb-4 p-4 bg-white rounded-lg border border-gray-200">
            <div className="flex items-center gap-2 mb-3">
              <Settings size={18} className="text-gray-500" />
              <span className="font-medium text-gray-700">配置选项</span>
            </div>
            
            <div className="grid grid-cols-2 md:grid-cols-3 gap-4">
              {/* Size */}
              <div>
                <label className="block text-sm font-medium text-gray-600 mb-1">尺寸</label>
                <select
                  value={config.size}
                  onChange={(e) => handleSizeChange(e.target.value as EmbedSize)}
                  className="w-full px-3 py-2 border border-gray-300 rounded-lg text-sm"
                >
                  <option value="small">小 (300px)</option>
                  <option value="medium">中 (450px)</option>
                  <option value="large">大 (600px)</option>
                  <option value="responsive">响应式</option>
                  <option value="custom">自定义</option>
                </select>
              </div>

              {/* Theme */}
              <div>
                <label className="block text-sm font-medium text-gray-600 mb-1">主题</label>
                <select
                  value={config.theme}
                  onChange={(e) => updateConfig({ theme: e.target.value as EmbedTheme })}
                  className="w-full px-3 py-2 border border-gray-300 rounded-lg text-sm"
                >
                  <option value="auto">自动</option>
                  <option value="light">浅色</option>
                  <option value="dark">深色</option>
                </select>
              </div>

              {/* Border Radius */}
              <div>
                <label className="block text-sm font-medium text-gray-600 mb-1">
                  圆角 ({config.borderRadius}px)
                </label>
                <input
                  type="range"
                  min="0"
                  max="24"
                  value={config.borderRadius}
                  onChange={(e) => updateConfig({ borderRadius: Number(e.target.value) })}
                  className="w-full"
                />
              </div>
            </div>

            {/* Toggles */}
            <div className="flex flex-wrap gap-4 mt-4">
              <label className="flex items-center gap-2 cursor-pointer">
                <input
                  type="checkbox"
                  checked={config.showHeader}
                  onChange={(e) => updateConfig({ showHeader: e.target.checked })}
                  className="rounded border-gray-300"
                />
                <span className="text-sm text-gray-600">显示标题</span>
              </label>
              <label className="flex items-center gap-2 cursor-pointer">
                <input
                  type="checkbox"
                  checked={config.showFooter}
                  onChange={(e) => updateConfig({ showFooter: e.target.checked })}
                  className="rounded border-gray-300"
                />
                <span className="text-sm text-gray-600">显示页脚</span>
              </label>
              <label className="flex items-center gap-2 cursor-pointer">
                <input
                  type="checkbox"
                  checked={config.allowFullscreen}
                  onChange={(e) => updateConfig({ allowFullscreen: e.target.checked })}
                  className="rounded border-gray-300"
                />
                <span className="text-sm text-gray-600">允许全屏</span>
              </label>
              <label className="flex items-center gap-2 cursor-pointer">
                <input
                  type="checkbox"
                  checked={config.border}
                  onChange={(e) => updateConfig({ border: e.target.checked })}
                  className="rounded border-gray-300"
                />
                <span className="text-sm text-gray-600">显示边框</span>
              </label>
              <label className="flex items-center gap-2 cursor-pointer">
                <input
                  type="checkbox"
                  checked={config.autoResize}
                  onChange={(e) => updateConfig({ autoResize: e.target.checked })}
                  className="rounded border-gray-300"
                />
                <span className="text-sm text-gray-600">自动调整高度</span>
              </label>
            </div>
          </div>

          {/* Code */}
          <div className="relative">
            <pre className="p-4 bg-gray-900 text-gray-100 text-sm rounded-lg overflow-x-auto">
              <code>{generateEmbedCode()}</code>
            </pre>
            <button
              onClick={handleCopy}
              className="absolute top-2 right-2 p-2 bg-white/10 hover:bg-white/20 rounded-lg text-white transition-colors"
            >
              {copied ? <Check size={18} /> : <Copy size={18} />}
            </button>
          </div>

          {/* oEmbed Link */}
          <div className="mt-4 p-3 bg-blue-50 rounded-lg">
            <p className="text-sm text-blue-800">
              <strong>oEmbed 端点：</strong>
              <code className="ml-2 bg-blue-100 px-2 py-1 rounded">
                {generateOEmbedUrl()}
              </code>
            </p>
            <p className="text-xs text-blue-600 mt-1">
              支持 WordPress、Medium 等平台自动嵌入
            </p>
          </div>
        </div>
      )}
    </div>
  );
};

// 嵌入式内容查看器（用于在 iframe 中显示）
export interface EmbedViewerProps {
  content: React.ReactNode;
  title?: string;
  showHeader?: boolean;
  showFooter?: boolean;
  theme?: EmbedTheme;
  allowInteraction?: boolean;
  className?: string;
}

export const EmbedViewer: React.FC<EmbedViewerProps> = ({
  content,
  title,
  showHeader = true,
  showFooter = false,
  theme = 'auto',
  allowInteraction = true,
  className = '',
}) => {
  const containerRef = useRef<HTMLDivElement>(null);

  // Report height to parent
  useEffect(() => {
    const reportHeight = () => {
      if (containerRef.current && window.parent !== window) {
        window.parent.postMessage({
          type: 'embed:resize',
          height: containerRef.current.scrollHeight,
        }, '*');
      }
    };

    reportHeight();
    window.addEventListener('resize', reportHeight);
    
    const observer = new MutationObserver(reportHeight);
    if (containerRef.current) {
      observer.observe(containerRef.current, { childList: true, subtree: true });
    }

    return () => {
      window.removeEventListener('resize', reportHeight);
      observer.disconnect();
    };
  }, []);

  const isDark = theme === 'dark' || 
    (theme === 'auto' && window.matchMedia('(prefers-color-scheme: dark)').matches);

  return (
    <div
      ref={containerRef}
      className={`
        min-h-screen
        ${isDark ? 'dark bg-gray-900 text-white' : 'bg-white text-gray-900'}
        ${className}
      `}
    >
      {showHeader && title && (
        <header className={`px-4 py-3 border-b ${isDark ? 'border-gray-700' : 'border-gray-200'}`}>
          <h1 className="font-semibold">{title}</h1>
        </header>
      )}
      
      <main className={`p-4 ${!allowInteraction ? 'pointer-events-none' : ''}`}>
        {content}
      </main>

      {showFooter && (
        <footer className={`px-4 py-3 border-t ${isDark ? 'border-gray-700' : 'border-gray-200'}`}>
          <div className="flex items-center justify-between">
            <span className="text-sm text-gray-500">Powered by FormalMath</span>
            <a 
              href={window.location.origin}
              target="_blank"
              rel="noopener noreferrer"
              className="flex items-center gap-1 text-sm text-blue-500 hover:text-blue-600"
            >
              访问网站 <ExternalLink size={14} />
            </a>
          </div>
        </footer>
      )}
    </div>
  );
};

export default ContentEmbed;
