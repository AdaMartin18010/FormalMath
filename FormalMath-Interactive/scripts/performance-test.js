/**
 * 性能测试脚本
 * 测试前端加载性能和API响应时间
 */

const puppeteer = require('puppeteer');
const fs = require('fs');
const path = require('path');

// 测试配置
const config = {
  baseUrl: process.env.TEST_URL || 'http://localhost:4173',
  iterations: 5,
  timeout: 60000,
  outputDir: path.join(__dirname, '../performance-reports'),
};

// 测试页面
const testPages = [
  { name: 'home', path: '/' },
  { name: 'knowledge-graph', path: '/knowledge-graph' },
  { name: 'reasoning-tree', path: '/reasoning-tree' },
  { name: 'mind-map', path: '/mind-map' },
  { name: 'analytics', path: '/analytics' },
  { name: 'proof-assistant', path: '/proof-assistant' },
];

// 性能指标收集器
class PerformanceCollector {
  constructor() {
    this.results = [];
  }

  addResult(page, metrics) {
    this.results.push({
      page,
      timestamp: new Date().toISOString(),
      ...metrics,
    });
  }

  getStats() {
    const stats = {};
    
    // 按页面分组统计
    const byPage = this.results.reduce((acc, r) => {
      if (!acc[r.page]) acc[r.page] = [];
      acc[r.page].push(r);
      return acc;
    }, {});

    for (const [page, results] of Object.entries(byPage)) {
      stats[page] = {
        samples: results.length,
        fcp: this.calculateStats(results.map(r => r.fcp)),
        lcp: this.calculateStats(results.map(r => r.lcp)),
        fid: this.calculateStats(results.map(r => r.fid)),
        cls: this.calculateStats(results.map(r => r.cls)),
        ttfb: this.calculateStats(results.map(r => r.ttfb)),
        loadTime: this.calculateStats(results.map(r => r.loadTime)),
        domContentLoaded: this.calculateStats(results.map(r => r.domContentLoaded)),
        resourceCount: this.calculateStats(results.map(r => r.resourceCount)),
        totalResourceSize: this.calculateStats(results.map(r => r.totalResourceSize)),
      };
    }

    return stats;
  }

  calculateStats(values) {
    const valid = values.filter(v => v !== undefined && v !== null && !isNaN(v));
    if (valid.length === 0) return null;

    const sorted = [...valid].sort((a, b) => a - b);
    const sum = valid.reduce((a, b) => a + b, 0);
    const mean = sum / valid.length;
    const variance = valid.reduce((sum, val) => sum + Math.pow(val - mean, 2), 0) / valid.length;

    return {
      min: sorted[0],
      max: sorted[sorted.length - 1],
      mean: Math.round(mean * 100) / 100,
      median: sorted[Math.floor(sorted.length / 2)],
      p75: sorted[Math.floor(sorted.length * 0.75)],
      p95: sorted[Math.floor(sorted.length * 0.95)],
      stdDev: Math.round(Math.sqrt(variance) * 100) / 100,
    };
  }

  saveReport() {
    if (!fs.existsSync(config.outputDir)) {
      fs.mkdirSync(config.outputDir, { recursive: true });
    }

    const report = {
      timestamp: new Date().toISOString(),
      config,
      summary: this.getStats(),
      rawData: this.results,
    };

    const filename = `performance-report-${Date.now()}.json`;
    fs.writeFileSync(
      path.join(config.outputDir, filename),
      JSON.stringify(report, null, 2)
    );

    // 生成 HTML 报告
    this.generateHtmlReport(report, filename.replace('.json', '.html'));

    return filename;
  }

  generateHtmlReport(report, filename) {
    const html = `
<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8">
  <title>Performance Report - ${new Date(report.timestamp).toLocaleString()}</title>
  <style>
    body { font-family: system-ui, sans-serif; max-width: 1200px; margin: 0 auto; padding: 20px; }
    h1, h2 { color: #333; }
    table { width: 100%; border-collapse: collapse; margin: 20px 0; }
    th, td { padding: 12px; text-align: left; border-bottom: 1px solid #ddd; }
    th { background: #f5f5f5; font-weight: 600; }
    tr:hover { background: #f9f9f9; }
    .metric-good { color: #22c55e; }
    .metric-warning { color: #f59e0b; }
    .metric-bad { color: #ef4444; }
    .stats-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 20px; }
    .stat-card { background: #f8fafc; padding: 20px; border-radius: 8px; }
    .stat-value { font-size: 32px; font-weight: bold; color: #3b82f6; }
    .stat-label { color: #64748b; margin-top: 4px; }
  </style>
</head>
<body>
  <h1>🚀 Performance Test Report</h1>
  <p>Generated: ${new Date(report.timestamp).toLocaleString()}</p>
  <p>URL: ${config.baseUrl}</p>
  
  <h2>Summary by Page</h2>
  <div class="stats-grid">
    ${Object.entries(report.summary).map(([page, stats]) => `
      <div class="stat-card">
        <h3>${page}</h3>
        <div class="stat-value ${this.getPerformanceClass(stats.lcp?.mean)}">
          ${stats.lcp?.mean ? Math.round(stats.lcp.mean) + 'ms' : 'N/A'}
        </div>
        <div class="stat-label">LCP (Largest Contentful Paint)</div>
        <table>
          <tr><td>FCP</td><td>${stats.fcp?.mean ? Math.round(stats.fcp.mean) + 'ms' : 'N/A'}</td></tr>
          <tr><td>TTFB</td><td>${stats.ttfb?.mean ? Math.round(stats.ttfb.mean) + 'ms' : 'N/A'}</td></tr>
          <tr><td>Load Time</td><td>${stats.loadTime?.mean ? Math.round(stats.loadTime.mean) + 'ms' : 'N/A'}</td></tr>
          <tr><td>Resources</td><td>${stats.resourceCount?.mean || 'N/A'}</td></tr>
        </table>
      </div>
    `).join('')}
  </div>

  <h2>Detailed Metrics</h2>
  ${Object.entries(report.summary).map(([page, stats]) => `
    <h3>${page}</h3>
    <table>
      <thead>
        <tr>
          <th>Metric</th>
          <th>Min</th>
          <th>Max</th>
          <th>Mean</th>
          <th>Median</th>
          <th>P75</th>
          <th>P95</th>
          <th>StdDev</th>
        </tr>
      </thead>
      <tbody>
        ${Object.entries(stats).filter(([k]) => k !== 'samples').map(([metric, values]) => `
          <tr>
            <td><strong>${metric}</strong></td>
            <td>${values ? Math.round(values.min) : 'N/A'}</td>
            <td>${values ? Math.round(values.max) : 'N/A'}</td>
            <td class="${this.getPerformanceClass(values?.mean, metric)}">${values ? Math.round(values.mean) : 'N/A'}</td>
            <td>${values ? Math.round(values.median) : 'N/A'}</td>
            <td>${values ? Math.round(values.p75) : 'N/A'}</td>
            <td>${values ? Math.round(values.p95) : 'N/A'}</td>
            <td>${values ? Math.round(values.stdDev) : 'N/A'}</td>
          </tr>
        `).join('')}
      </tbody>
    </table>
  `).join('')}
</body>
</html>`;

    fs.writeFileSync(path.join(config.outputDir, filename), html);
  }

  getPerformanceClass(value, metric = 'lcp') {
    if (value === undefined || value === null) return '';
    
    // LCP thresholds
    if (metric === 'lcp' || metric === 'fcp') {
      if (value < 1800) return 'metric-good';
      if (value < 3000) return 'metric-warning';
      return 'metric-bad';
    }
    
    // TTFB thresholds
    if (metric === 'ttfb') {
      if (value < 600) return 'metric-good';
      if (value < 1000) return 'metric-warning';
      return 'metric-bad';
    }
    
    return '';
  }
}

// 运行测试
async function runTests() {
  console.log('🚀 Starting performance tests...\n');

  const browser = await puppeteer.launch({
    headless: 'new',
    args: ['--no-sandbox', '--disable-setuid-sandbox'],
  });

  const collector = new PerformanceCollector();

  try {
    for (const pageConfig of testPages) {
      console.log(`Testing ${pageConfig.name}...`);

      for (let i = 0; i < config.iterations; i++) {
        const page = await browser.newPage();
        
        // 启用性能追踪
        await page.evaluateOnNewDocument(() => {
          window.performanceMarks = {};
        });

        try {
          const url = `${config.baseUrl}${pageConfig.path}`;
          const startTime = Date.now();

          await page.goto(url, {
            waitUntil: 'networkidle0',
            timeout: config.timeout,
          });

          // 收集性能指标
          const metrics = await page.evaluate(() => {
            const perf = window.performance;
            const nav = perf.getEntriesByType('navigation')[0];
            const paint = perf.getEntriesByType('paint');
            const lcp = perf.getEntriesByType('largest-contentful-paint');
            
            const fcp = paint.find(p => p.name === 'first-contentful-paint');
            
            return {
              fcp: fcp?.startTime,
              lcp: lcp[lcp.length - 1]?.startTime,
              ttfb: nav?.responseStart - nav?.startTime,
              loadTime: nav?.loadEventEnd - nav?.startTime,
              domContentLoaded: nav?.domContentLoadedEventEnd - nav?.startTime,
              resourceCount: perf.getEntriesByType('resource').length,
              totalResourceSize: perf.getEntriesByType('resource').reduce(
                (sum, r) => sum + (r.transferSize || 0), 0
              ),
            };
          });

          collector.addResult(pageConfig.name, metrics);
          
          process.stdout.write(`  ✓ Iteration ${i + 1}/${config.iterations} - LCP: ${Math.round(metrics.lcp || 0)}ms\n`);
        } catch (error) {
          console.error(`  ✗ Iteration ${i + 1} failed:`, error.message);
        } finally {
          await page.close();
        }
      }

      console.log('');
    }

    // 生成报告
    const reportFile = collector.saveReport();
    const stats = collector.getStats();

    // 打印摘要
    console.log('\n📊 Performance Summary');
    console.log('=' .repeat(60));
    
    for (const [page, metrics] of Object.entries(stats)) {
      console.log(`\n${page}:`);
      console.log(`  LCP: ${metrics.lcp?.mean ? Math.round(metrics.lcp.mean) + 'ms' : 'N/A'}`);
      console.log(`  FCP: ${metrics.fcp?.mean ? Math.round(metrics.fcp.mean) + 'ms' : 'N/A'}`);
      console.log(`  TTFB: ${metrics.ttfb?.mean ? Math.round(metrics.ttfb.mean) + 'ms' : 'N/A'}`);
      console.log(`  Load Time: ${metrics.loadTime?.mean ? Math.round(metrics.loadTime.mean) + 'ms' : 'N/A'}`);
    }

    console.log(`\n📄 Report saved: ${path.join(config.outputDir, reportFile)}`);

  } finally {
    await browser.close();
  }
}

// 运行测试
runTests().catch(console.error);
