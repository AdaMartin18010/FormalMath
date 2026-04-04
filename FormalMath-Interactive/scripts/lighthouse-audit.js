/**
 * Lighthouse 性能审计脚本
 * 使用 Lighthouse 进行全面的性能分析
 */

const lighthouse = require('lighthouse');
const chromeLauncher = require('chrome-launcher');
const fs = require('fs');
const path = require('path');

// 配置
const config = {
  baseUrl: process.env.TEST_URL || 'http://localhost:4173',
  outputDir: path.join(__dirname, '../performance-reports'),
  formFactor: 'desktop', // 'desktop' | 'mobile'
  throttling: 'simulated4G', // 'simulate3G' | 'simulated4G' | 'devtools'
  categories: ['performance', 'accessibility', 'best-practices', 'seo', 'pwa'],
};

// 测试页面
const testPages = [
  { name: 'home', path: '/' },
  { name: 'knowledge-graph', path: '/knowledge-graph' },
  { name: 'reasoning-tree', path: '/reasoning-tree' },
  { name: 'analytics', path: '/analytics' },
];

// 运行 Lighthouse 审计
async function runLighthouse(url, options = {}) {
  const chrome = await chromeLauncher.launch({
    chromeFlags: ['--headless', '--no-sandbox', '--disable-gpu'],
  });

  const lighthouseConfig = {
    extends: 'lighthouse:default',
    settings: {
      formFactor: options.formFactor || config.formFactor,
      throttling: {
        rttMs: options.throttling === 'simulate3G' ? 150 : 40,
        throughputKbps: options.throttling === 'simulate3G' ? 1.6 * 1024 : 10 * 1024,
        cpuSlowdownMultiplier: options.formFactor === 'mobile' ? 4 : 1,
      },
      screenEmulation: {
        mobile: options.formFactor === 'mobile',
        width: options.formFactor === 'mobile' ? 360 : 1350,
        height: options.formFactor === 'mobile' ? 640 : 940,
        deviceScaleFactor: options.formFactor === 'mobile' ? 2 : 1,
        disabled: false,
      },
      emulatedUserAgent: options.formFactor === 'mobile'
        ? 'Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36'
        : 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
    },
  };

  try {
    const runnerResult = await lighthouse(url, {
      port: chrome.port,
      output: ['json', 'html'],
      onlyCategories: config.categories,
    }, lighthouseConfig);

    await chrome.kill();

    return runnerResult;
  } catch (error) {
    await chrome.kill();
    throw error;
  }
}

// 分析结果
function analyzeReport(report, pageName) {
  const categories = report.categories;
  const audits = report.audits;

  return {
    page: pageName,
    url: report.finalUrl,
    scores: {
      performance: Math.round(categories.performance?.score * 100) || 0,
      accessibility: Math.round(categories.accessibility?.score * 100) || 0,
      bestPractices: Math.round(categories['best-practices']?.score * 100) || 0,
      seo: Math.round(categories.seo?.score * 100) || 0,
      pwa: Math.round(categories.pwa?.score * 100) || 0,
    },
    metrics: {
      lcp: audits['largest-contentful-paint']?.numericValue,
      fcp: audits['first-contentful-paint']?.numericValue,
      ttfb: audits['server-response-time']?.numericValue,
      cls: audits['cumulative-layout-shift']?.numericValue,
      tbt: audits['total-blocking-time']?.numericValue,
      speedIndex: audits['speed-index']?.numericValue,
      interactive: audits['interactive']?.numericValue,
    },
    opportunities: Object.values(audits)
      .filter(audit => audit.details?.type === 'opportunity' && audit.numericValue > 0)
      .map(audit => ({
        title: audit.title,
        description: audit.description,
        score: audit.score,
        savings: audit.numericValue,
      })),
    diagnostics: Object.values(audits)
      .filter(audit => audit.details?.type === 'table' && audit.score !== null && audit.score < 1)
      .map(audit => ({
        title: audit.title,
        description: audit.description,
        score: audit.score,
      })),
  };
}

// 生成优化建议
function generateRecommendations(results) {
  const recommendations = [];

  // 性能建议
  const avgPerformance = results.reduce((sum, r) => sum + r.scores.performance, 0) / results.length;
  
  if (avgPerformance < 90) {
    recommendations.push({
      category: 'Performance',
      priority: 'high',
      title: '提升整体性能评分',
      description: `当前平均性能评分为 ${avgPerformance}%，建议优化资源加载和代码分割。`,
      actions: [
        '启用更激进的代码分割策略',
        '优化关键渲染路径',
        '延迟加载非关键资源',
        '使用 Service Worker 缓存静态资源',
      ],
    });
  }

  // 检查 LCP
  const avgLCP = results.reduce((sum, r) => sum + (r.metrics.lcp || 0), 0) / results.length;
  if (avgLCP > 2500) {
    recommendations.push({
      category: 'LCP',
      priority: 'high',
      title: '优化最大内容绘制时间',
      description: `当前平均 LCP 为 ${Math.round(avgLCP)}ms，建议控制在 2500ms 以内。`,
      actions: [
        '优化首屏图片加载（使用 WebP/AVIF 格式）',
        '预加载关键资源',
        '使用 CDN 分发静态资源',
        '优化服务器响应时间',
      ],
    });
  }

  // 检查 CLS
  const maxCLS = Math.max(...results.map(r => r.metrics.cls || 0));
  if (maxCLS > 0.1) {
    recommendations.push({
      category: 'CLS',
      priority: 'medium',
      title: '减少累积布局偏移',
      description: `检测到最大 CLS 为 ${maxCLS.toFixed(3)}，建议控制在 0.1 以内。`,
      actions: [
        '为图片和广告预留空间',
        '避免在内容上方插入动态内容',
        '使用 font-display: swap 处理 Web 字体',
      ],
    });
  }

  // 检查 TBT
  const avgTBT = results.reduce((sum, r) => sum + (r.metrics.tbt || 0), 0) / results.length;
  if (avgTBT > 200) {
    recommendations.push({
      category: 'TBT',
      priority: 'medium',
      title: '减少总阻塞时间',
      description: `当前平均 TBT 为 ${Math.round(avgTBT)}ms，建议控制在 200ms 以内。`,
      actions: [
        '减少 JavaScript 执行时间',
        '代码分割和懒加载',
        '优化第三方脚本加载',
        '使用 Web Workers 处理复杂计算',
      ],
    });
  }

  return recommendations;
}

// 保存报告
function saveReport(results, recommendations) {
  if (!fs.existsSync(config.outputDir)) {
    fs.mkdirSync(config.outputDir, { recursive: true });
  }

  const timestamp = Date.now();
  const report = {
    timestamp: new Date().toISOString(),
    config,
    summary: {
      averageScores: {
        performance: Math.round(results.reduce((sum, r) => sum + r.scores.performance, 0) / results.length),
        accessibility: Math.round(results.reduce((sum, r) => sum + r.scores.accessibility, 0) / results.length),
        bestPractices: Math.round(results.reduce((sum, r) => sum + r.scores.bestPractices, 0) / results.length),
        seo: Math.round(results.reduce((sum, r) => sum + r.scores.seo, 0) / results.length),
        pwa: Math.round(results.reduce((sum, r) => sum + r.scores.pwa, 0) / results.length),
      },
      averageMetrics: {
        lcp: Math.round(results.reduce((sum, r) => sum + (r.metrics.lcp || 0), 0) / results.length),
        fcp: Math.round(results.reduce((sum, r) => sum + (r.metrics.fcp || 0), 0) / results.length),
        ttfb: Math.round(results.reduce((sum, r) => sum + (r.metrics.ttfb || 0), 0) / results.length),
        cls: (results.reduce((sum, r) => sum + (r.metrics.cls || 0), 0) / results.length).toFixed(3),
      },
    },
    results,
    recommendations,
  };

  // 保存 JSON
  fs.writeFileSync(
    path.join(config.outputDir, `lighthouse-report-${timestamp}.json`),
    JSON.stringify(report, null, 2)
  );

  // 生成 HTML 报告
  generateHtmlReport(report, `lighthouse-report-${timestamp}.html`);

  return report;
}

// 生成 HTML 报告
function generateHtmlReport(report, filename) {
  const getScoreClass = (score) => {
    if (score >= 90) return 'good';
    if (score >= 50) return 'average';
    return 'poor';
  };

  const html = `
<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8">
  <title>Lighthouse Performance Report</title>
  <style>
    * { box-sizing: border-box; }
    body { 
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
      max-width: 1200px; 
      margin: 0 auto; 
      padding: 20px;
      background: #f5f5f5;
    }
    h1, h2, h3 { color: #333; margin-top: 0; }
    .header { 
      background: white; 
      padding: 30px; 
      border-radius: 12px; 
      margin-bottom: 20px;
      box-shadow: 0 2px 4px rgba(0,0,0,0.1);
    }
    .summary-grid { 
      display: grid; 
      grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); 
      gap: 20px; 
      margin: 20px 0;
    }
    .score-card { 
      background: white;
      padding: 24px; 
      border-radius: 12px; 
      text-align: center;
      box-shadow: 0 2px 4px rgba(0,0,0,0.1);
    }
    .score-value { 
      font-size: 48px; 
      font-weight: bold; 
      margin: 10px 0;
    }
    .score-value.good { color: #0cce6b; }
    .score-value.average { color: #ffa400; }
    .score-value.poor { color: #ff4e42; }
    .score-label { color: #666; font-size: 14px; }
    .page-result { 
      background: white; 
      padding: 24px; 
      border-radius: 12px; 
      margin-bottom: 20px;
      box-shadow: 0 2px 4px rgba(0,0,0,0.1);
    }
    .metrics-grid {
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
      gap: 16px;
      margin: 20px 0;
    }
    .metric-box {
      background: #f8f9fa;
      padding: 16px;
      border-radius: 8px;
    }
    .metric-value {
      font-size: 24px;
      font-weight: bold;
      color: #333;
    }
    .metric-label {
      font-size: 12px;
      color: #666;
      margin-top: 4px;
    }
    .recommendations {
      background: white;
      padding: 24px;
      border-radius: 12px;
      box-shadow: 0 2px 4px rgba(0,0,0,0.1);
    }
    .recommendation {
      border-left: 4px solid #ff4e42;
      padding-left: 16px;
      margin: 16px 0;
    }
    .recommendation.high { border-color: #ff4e42; }
    .recommendation.medium { border-color: #ffa400; }
    .recommendation.low { border-color: #0cce6b; }
    .priority-badge {
      display: inline-block;
      padding: 4px 8px;
      border-radius: 4px;
      font-size: 12px;
      font-weight: bold;
      margin-bottom: 8px;
    }
    .priority-high { background: #ff4e42; color: white; }
    .priority-medium { background: #ffa400; color: white; }
    .priority-low { background: #0cce6b; color: white; }
    .actions-list {
      margin: 12px 0;
      padding-left: 20px;
    }
    .actions-list li {
      margin: 8px 0;
      color: #555;
    }
  </style>
</head>
<body>
  <div class="header">
    <h1>🚦 Lighthouse Performance Report</h1>
    <p>Generated: ${new Date(report.timestamp).toLocaleString()}</p>
    <p>Form Factor: ${config.formFactor} | Throttling: ${config.throttling}</p>
  </div>

  <div class="summary-grid">
    ${Object.entries(report.summary.averageScores).map(([name, score]) => `
      <div class="score-card">
        <div class="score-label">${name.toUpperCase()}</div>
        <div class="score-value ${getScoreClass(score)}">${score}</div>
      </div>
    `).join('')}
  </div>

  <h2>Page Results</h2>
  ${report.results.map(page => `
    <div class="page-result">
      <h3>${page.page} <small style="color: #666;">${page.url}</small></h3>
      <div class="metrics-grid">
        <div class="metric-box">
          <div class="metric-value">${page.scores.performance}</div>
          <div class="metric-label">Performance</div>
        </div>
        <div class="metric-box">
          <div class="metric-value">${Math.round(page.metrics.lcp || 0)}ms</div>
          <div class="metric-label">LCP</div>
        </div>
        <div class="metric-box">
          <div class="metric-value">${Math.round(page.metrics.fcp || 0)}ms</div>
          <div class="metric-label">FCP</div>
        </div>
        <div class="metric-box">
          <div class="metric-value">${(page.metrics.cls || 0).toFixed(3)}</div>
          <div class="metric-label">CLS</div>
        </div>
        <div class="metric-box">
          <div class="metric-value">${Math.round(page.metrics.ttfb || 0)}ms</div>
          <div class="metric-label">TTFB</div>
        </div>
      </div>
    </div>
  `).join('')}

  <div class="recommendations">
    <h2>🎯 Optimization Recommendations</h2>
    ${report.recommendations.map(rec => `
      <div class="recommendation ${rec.priority}">
        <span class="priority-badge priority-${rec.priority}">${rec.priority.toUpperCase()}</span>
        <h3>${rec.title}</h3>
        <p>${rec.description}</p>
        <ul class="actions-list">
          ${rec.actions.map(action => `<li>${action}</li>`).join('')}
        </ul>
      </div>
    `).join('')}
  </div>
</body>
</html>`;

  fs.writeFileSync(path.join(config.outputDir, filename), html);
}

// 主函数
async function main() {
  console.log('🚦 Starting Lighthouse audit...\n');

  const results = [];

  for (const page of testPages) {
    console.log(`Auditing ${page.name}...`);
    
    try {
      const url = `${config.baseUrl}${page.path}`;
      const runnerResult = await runLighthouse(url);
      
      // 保存 HTML 报告
      const htmlReport = runnerResult.report[1];
      fs.writeFileSync(
        path.join(config.outputDir, `lighthouse-${page.name}.html`),
        htmlReport
      );

      // 分析结果
      const analysis = analyzeReport(runnerResult.lhr, page.name);
      results.push(analysis);

      console.log(`  ✓ Performance: ${analysis.scores.performance}`);
      console.log(`  ✓ LCP: ${Math.round(analysis.metrics.lcp || 0)}ms`);
      console.log(`  ✓ CLS: ${(analysis.metrics.cls || 0).toFixed(3)}`);
      console.log('');
    } catch (error) {
      console.error(`  ✗ Failed:`, error.message);
    }
  }

  // 生成优化建议
  const recommendations = generateRecommendations(results);

  // 保存报告
  const report = saveReport(results, recommendations);

  // 打印摘要
  console.log('\n📊 Audit Summary');
  console.log('=' .repeat(60));
  console.log(`Performance: ${report.summary.averageScores.performance}/100`);
  console.log(`Accessibility: ${report.summary.averageScores.accessibility}/100`);
  console.log(`Best Practices: ${report.summary.averageScores.bestPractices}/100`);
  console.log(`SEO: ${report.summary.averageScores.seo}/100`);
  console.log(`\nLCP: ${report.summary.averageMetrics.lcp}ms`);
  console.log(`FCP: ${report.summary.averageMetrics.fcp}ms`);
  console.log(`CLS: ${report.summary.averageMetrics.cls}`);

  if (recommendations.length > 0) {
    console.log(`\n🎯 Top Recommendations:`);
    recommendations.slice(0, 3).forEach((rec, i) => {
      console.log(`  ${i + 1}. ${rec.title}`);
    });
  }
}

main().catch(console.error);
