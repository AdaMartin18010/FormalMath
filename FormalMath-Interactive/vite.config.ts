import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'
import path from 'path'

// https://vitejs.dev/config/
export default defineConfig({
  plugins: [react()],
  resolve: {
    alias: {
      '@': path.resolve(__dirname, './src'),
    },
  },
  build: {
    outDir: 'dist',
    sourcemap: true,
    rollupOptions: {
      output: {
        manualChunks: {
          vendor: ['react', 'react-dom'],
          d3: ['d3', 'd3-selection', 'd3-scale', 'd3-hierarchy'],
          mermaid: ['mermaid'],
          utils: ['lodash-es', 'date-fns'],
        },
        // 优化资源文件命名
        assetFileNames: (assetInfo) => {
          const info = assetInfo.name.split('.')
          const ext = info[info.length - 1]
          if (/\.(png|jpe?g|gif|svg|webp|ico)$/i.test(assetInfo.name)) {
            return 'assets/images/[name]-[hash][extname]'
          }
          if (/\.(woff2?|ttf|otf|eot)$/i.test(assetInfo.name)) {
            return 'assets/fonts/[name]-[hash][extname]'
          }
          return 'assets/[name]-[hash][extname]'
        },
        chunkFileNames: 'assets/js/[name]-[hash].js',
        entryFileNames: 'assets/js/[name]-[hash].js',
      },
    },
    // 优化构建性能
    target: 'es2020',
    minify: 'terser',
    terserOptions: {
      compress: {
        drop_console: true,
        drop_debugger: true,
      },
    },
    // 启用 gzip 压缩报告
    reportCompressedSize: true,
    //  chunk 大小警告阈值
    chunkSizeWarningLimit: 1000,
  },
  // 生产环境基础路径（GitHub Pages）
  base: '/FormalMath/',
  // 开发服务器配置
  server: {
    port: 3000,
    host: true,
    open: true,
    proxy: {
      '/api': {
        target: 'http://localhost:8000',
        changeOrigin: true,
        rewrite: (path) => path.replace(/^\/api/, ''),
      },
    },
  },
  // 预览服务器配置
  preview: {
    port: 4173,
    host: true,
  },
  // CSS 配置
  css: {
    devSourcemap: true,
    preprocessorOptions: {
      scss: {
        additionalData: `@use "@/styles/variables.scss" as *;`,
      },
    },
  },
  // 优化依赖预构建
  optimizeDeps: {
    include: ['react', 'react-dom', 'd3', 'mermaid', 'lodash-es'],
    exclude: ['@ FormalMath/concept'],
  },
})
