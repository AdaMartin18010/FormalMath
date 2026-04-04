import React from 'react';
import { 
  Github, 
  Twitter, 
  Mail, 
  Heart, 
  ExternalLink,
  BookOpen,
  Code,
  MessageCircle
} from 'lucide-react';

export const Footer: React.FC = () => {
  const currentYear = new Date().getFullYear();

  const footerLinks = {
    product: [
      { label: '功能介绍', href: '/features' },
      { label: '使用文档', href: '/docs' },
      { label: 'API文档', href: '/api-docs' },
      { label: '更新日志', href: '/changelog' },
    ],
    resources: [
      { label: '数学知识库', href: '/knowledge' },
      { label: '可视化示例', href: '/examples' },
      { label: '数据集下载', href: '/datasets' },
      { label: '学术论文', href: '/papers' },
    ],
    community: [
      { label: 'GitHub', href: 'https://github.com/formalmath', icon: <Github className="w-4 h-4" /> },
      { label: '讨论区', href: '/discussions', icon: <MessageCircle className="w-4 h-4" /> },
      { label: '贡献指南', href: '/contribute', icon: <Code className="w-4 h-4" /> },
      { label: '学习资源', href: '/learn', icon: <BookOpen className="w-4 h-4" /> },
    ],
    legal: [
      { label: '隐私政策', href: '/privacy' },
      { label: '使用条款', href: '/terms' },
      { label: '许可证', href: '/license' },
    ],
  };

  return (
    <footer className="bg-gray-900 text-gray-300">
      {/* Main Footer */}
      <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 py-12">
        <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-5 gap-8">
          {/* Brand */}
          <div className="lg:col-span-2">
            <div className="flex items-center gap-2 mb-4">
              <div className="flex items-center justify-center w-10 h-10 bg-blue-600 rounded-lg">
                <span className="text-xl font-bold text-white">F</span>
              </div>
              <div>
                <h2 className="text-lg font-bold text-white">FormalMath</h2>
                <p className="text-xs text-gray-400">交互式数学可视化平台</p>
              </div>
            </div>
            <p className="text-sm text-gray-400 mb-4 max-w-xs">
              FormalMath致力于构建结构化的数学知识体系，通过交互式可视化帮助学习者深入理解数学概念之间的关联。
            </p>
            <div className="flex items-center gap-4">
              <a
                href="https://github.com/formalmath"
                target="_blank"
                rel="noopener noreferrer"
                className="text-gray-400 hover:text-white transition-colors"
                aria-label="GitHub"
              >
                <Github className="w-5 h-5" />
              </a>
              <a
                href="https://twitter.com/formalmath"
                target="_blank"
                rel="noopener noreferrer"
                className="text-gray-400 hover:text-white transition-colors"
                aria-label="Twitter"
              >
                <Twitter className="w-5 h-5" />
              </a>
              <a
                href="mailto:contact@formalmath.org"
                className="text-gray-400 hover:text-white transition-colors"
                aria-label="Email"
              >
                <Mail className="w-5 h-5" />
              </a>
            </div>
          </div>

          {/* Product Links */}
          <div>
            <h3 className="text-sm font-semibold text-white uppercase tracking-wider mb-4">
              产品
            </h3>
            <ul className="space-y-2">
              {footerLinks.product.map(link => (
                <li key={link.label}>
                  <a
                    href={link.href}
                    className="text-sm text-gray-400 hover:text-white transition-colors"
                  >
                    {link.label}
                  </a>
                </li>
              ))}
            </ul>
          </div>

          {/* Resources Links */}
          <div>
            <h3 className="text-sm font-semibold text-white uppercase tracking-wider mb-4">
              资源
            </h3>
            <ul className="space-y-2">
              {footerLinks.resources.map(link => (
                <li key={link.label}>
                  <a
                    href={link.href}
                    className="text-sm text-gray-400 hover:text-white transition-colors"
                  >
                    {link.label}
                  </a>
                </li>
              ))}
            </ul>
          </div>

          {/* Community Links */}
          <div>
            <h3 className="text-sm font-semibold text-white uppercase tracking-wider mb-4">
              社区
            </h3>
            <ul className="space-y-2">
              {footerLinks.community.map(link => (
                <li key={link.label}>
                  <a
                    href={link.href}
                    target={link.href.startsWith('http') ? '_blank' : undefined}
                    rel={link.href.startsWith('http') ? 'noopener noreferrer' : undefined}
                    className="text-sm text-gray-400 hover:text-white transition-colors inline-flex items-center gap-1"
                  >
                    {link.label}
                    {link.href.startsWith('http') && <ExternalLink className="w-3 h-3" />}
                  </a>
                </li>
              ))}
            </ul>
          </div>
        </div>
      </div>

      {/* Bottom Bar */}
      <div className="border-t border-gray-800">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 py-4">
          <div className="flex flex-col md:flex-row items-center justify-between gap-4">
            <p className="text-sm text-gray-500">
              &copy; {currentYear} FormalMath. 保留所有权利。
            </p>
            <div className="flex items-center gap-6">
              {footerLinks.legal.map(link => (
                <a
                  key={link.label}
                  href={link.href}
                  className="text-sm text-gray-500 hover:text-gray-300 transition-colors"
                >
                  {link.label}
                </a>
              ))}
            </div>
            <p className="text-sm text-gray-500 flex items-center gap-1">
              用 <Heart className="w-4 h-4 text-red-500" /> 构建
            </p>
          </div>
        </div>
      </div>
    </footer>
  );
};

export default Footer;
