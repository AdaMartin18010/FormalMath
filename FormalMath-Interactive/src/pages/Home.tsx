import React from 'react';
import { Link } from 'react-router-dom';
import { 
  Network, 
  GitBranch, 
  Brain, 
  BarChart3, 
  Layout, 
  History,
  ArrowRight,
  Sparkles,
  BookOpen,
  Zap,
  Shield
} from 'lucide-react';
import { cn } from '@utils/classNames';

interface FeatureCardProps {
  icon: React.ReactNode;
  title: string;
  description: string;
  to: string;
  color: string;
}

const FeatureCard: React.FC<FeatureCardProps> = ({ icon, title, description, to, color }) => (
  <Link
    to={to}
    className={cn(
      'group relative p-6 bg-white rounded-xl border border-gray-200 shadow-sm',
      'hover:shadow-lg hover:border-blue-300 transition-all duration-300'
    )}
  >
    <div className={cn('w-12 h-12 rounded-lg flex items-center justify-center mb-4', color)}>
      {icon}
    </div>
    <h3 className="text-lg font-semibold text-gray-900 mb-2 group-hover:text-blue-600 transition-colors">
      {title}
    </h3>
    <p className="text-sm text-gray-500 mb-4">{description}</p>
    <div className="flex items-center text-sm text-blue-600 font-medium">
      开始使用
      <ArrowRight className="w-4 h-4 ml-1 group-hover:translate-x-1 transition-transform" />
    </div>
  </Link>
);

const features = [
  {
    icon: <Network className="w-6 h-6 text-white" />,
    title: '知识图谱',
    description: '探索数学概念之间的关联网络，可视化知识结构，发现隐藏的联系。',
    to: '/knowledge-graph',
    color: 'bg-blue-500',
  },
  {
    icon: <GitBranch className="w-6 h-6 text-white" />,
    title: '推理树',
    description: '追踪数学证明的推理路径，理解从假设到结论的逻辑链条。',
    to: '/reasoning-tree',
    color: 'bg-green-500',
  },
  {
    icon: <Brain className="w-6 h-6 text-white" />,
    title: '思维导图',
    description: '以层级结构组织数学知识，从宏观到微观逐步深入理解。',
    to: '/mind-map',
    color: 'bg-purple-500',
  },
  {
    icon: <BarChart3 className="w-6 h-6 text-white" />,
    title: '对比分析',
    description: '并排比较不同的数学理论、方法和结果，发现异同点。',
    to: '/comparison',
    color: 'bg-orange-500',
  },
  {
    icon: <Layout className="w-6 h-6 text-white" />,
    title: '决策树',
    description: '基于条件判断探索数学问题的解决方案，找到最优路径。',
    to: '/decision-tree',
    color: 'bg-pink-500',
  },
  {
    icon: <History className="w-6 h-6 text-white" />,
    title: '演化历史',
    description: '追溯数学理论的发展历程，了解知识是如何演进的。',
    to: '/evolution',
    color: 'bg-indigo-500',
  },
];

const stats = [
  { label: '数学概念', value: '3,500+', icon: BookOpen },
  { label: '定理证明', value: '1,200+', icon: Shield },
  { label: '知识关联', value: '8,900+', icon: Network },
  { label: '日活跃用户', value: '2,400+', icon: Zap },
];

export const Home: React.FC = () => {
  return (
    <div className="min-h-screen bg-gray-50">
      {/* Hero Section */}
      <section className="relative overflow-hidden bg-gradient-to-br from-blue-600 via-blue-700 to-indigo-800 text-white">
        <div className="absolute inset-0 opacity-10">
          <div className="absolute inset-0" style={{
            backgroundImage: `url("data:image/svg+xml,%3Csvg width='60' height='60' viewBox='0 0 60 60' xmlns='http://www.w3.org/2000/svg'%3E%3Cg fill='none' fill-rule='evenodd'%3E%3Cg fill='%23ffffff' fill-opacity='0.4'%3E%3Cpath d='M36 34v-4h-2v4h-4v2h4v4h2v-4h4v-2h-4zm0-30V0h-2v4h-4v2h4v4h2V6h4V4h-4zM6 34v-4H4v4H0v2h4v4h2v-4h4v-2H6zM6 4V0H4v4H0v2h4v4h2V6h4V4H6z'/%3E%3C/g%3E%3C/g%3E%3C/svg%3E")`,
          }} />
        </div>
        
        <div className="relative max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 py-24 lg:py-32">
          <div className="text-center max-w-3xl mx-auto">
            <div className="inline-flex items-center gap-2 px-4 py-2 bg-white/10 backdrop-blur rounded-full text-sm font-medium mb-6">
              <Sparkles className="w-4 h-4" />
              <span>基于 React + D3.js + Mermaid.js 构建</span>
            </div>
            <h1 className="text-4xl sm:text-5xl lg:text-6xl font-bold mb-6 tracking-tight">
              FormalMath 交互式
              <span className="block text-blue-200">可视化平台</span>
            </h1>
            <p className="text-lg sm:text-xl text-blue-100 mb-8 leading-relaxed">
              通过现代化的交互式可视化技术，探索数学知识的结构与联系。
              从概念图谱到推理树，从对比分析到演化历史，全方位理解数学之美。
            </p>
            <div className="flex flex-col sm:flex-row items-center justify-center gap-4">
              <Link
                to="/knowledge-graph"
                className="w-full sm:w-auto px-8 py-4 bg-white text-blue-700 font-semibold rounded-xl hover:bg-blue-50 transition-colors shadow-lg"
              >
                开始探索
              </Link>
              <Link
                to="/docs"
                className="w-full sm:w-auto px-8 py-4 bg-blue-600/50 backdrop-blur text-white font-semibold rounded-xl hover:bg-blue-600/70 transition-colors border border-white/20"
              >
                查看文档
              </Link>
            </div>
          </div>
        </div>

        {/* Wave Divider */}
        <div className="absolute bottom-0 left-0 right-0">
          <svg viewBox="0 0 1440 120" fill="none" xmlns="http://www.w3.org/2000/svg">
            <path d="M0 120L60 105C120 90 240 60 360 45C480 30 600 30 720 37.5C840 45 960 60 1080 67.5C1200 75 1320 75 1380 75L1440 75V120H1380C1320 120 1200 120 1080 120C960 120 840 120 720 120C600 120 480 120 360 120C240 120 120 120 60 120H0Z" fill="#F9FAFB"/>
          </svg>
        </div>
      </section>

      {/* Stats Section */}
      <section className="py-12 bg-gray-50">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
          <div className="grid grid-cols-2 lg:grid-cols-4 gap-4">
            {stats.map((stat, index) => (
              <div
                key={index}
                className="bg-white p-6 rounded-xl border border-gray-200 shadow-sm text-center"
              >
                <stat.icon className="w-8 h-8 text-blue-600 mx-auto mb-3" />
                <div className="text-3xl font-bold text-gray-900 mb-1">{stat.value}</div>
                <div className="text-sm text-gray-500">{stat.label}</div>
              </div>
            ))}
          </div>
        </div>
      </section>

      {/* Features Section */}
      <section className="py-16 bg-gray-50">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
          <div className="text-center mb-12">
            <h2 className="text-3xl font-bold text-gray-900 mb-4">核心功能</h2>
            <p className="text-lg text-gray-600 max-w-2xl mx-auto">
              FormalMath 提供多种可视化工具，帮助您以不同的视角理解数学知识
            </p>
          </div>
          <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
            {features.map((feature, index) => (
              <FeatureCard key={index} {...feature} />
            ))}
          </div>
        </div>
      </section>

      {/* Tech Stack Section */}
      <section className="py-16 bg-white">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
          <div className="text-center mb-12">
            <h2 className="text-3xl font-bold text-gray-900 mb-4">技术栈</h2>
            <p className="text-lg text-gray-600">基于现代前端技术构建的高性能可视化平台</p>
          </div>
          <div className="flex flex-wrap justify-center gap-4">
            {[
              { name: 'React 18', color: 'bg-blue-100 text-blue-700' },
              { name: 'TypeScript', color: 'bg-blue-100 text-blue-700' },
              { name: 'D3.js v7', color: 'bg-orange-100 text-orange-700' },
              { name: 'Mermaid.js', color: 'bg-green-100 text-green-700' },
              { name: 'Tailwind CSS', color: 'bg-cyan-100 text-cyan-700' },
              { name: 'Vite', color: 'bg-purple-100 text-purple-700' },
            ].map((tech, index) => (
              <span
                key={index}
                className={cn(
                  'px-4 py-2 rounded-lg font-medium',
                  tech.color
                )}
              >
                {tech.name}
              </span>
            ))}
          </div>
        </div>
      </section>

      {/* CTA Section */}
      <section className="py-16 bg-gray-900 text-white">
        <div className="max-w-4xl mx-auto px-4 sm:px-6 lg:px-8 text-center">
          <h2 className="text-3xl font-bold mb-4">准备好开始探索了吗？</h2>
          <p className="text-lg text-gray-400 mb-8">
            立即体验 FormalMath 交互式可视化平台，发现数学知识的新视角
          </p>
          <Link
            to="/knowledge-graph"
            className="inline-flex items-center gap-2 px-8 py-4 bg-blue-600 text-white font-semibold rounded-xl hover:bg-blue-700 transition-colors"
          >
            <Sparkles className="w-5 h-5" />
            立即开始
          </Link>
        </div>
      </section>
    </div>
  );
};

export default Home;
