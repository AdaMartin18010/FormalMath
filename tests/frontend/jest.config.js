/** @type {import('jest').Config} */
module.exports = {
  // 根目录
  rootDir: '../../FormalMath-Interactive',
  
  // 测试环境
  testEnvironment: 'jsdom',
  
  // 文件扩展名
  moduleFileExtensions: ['ts', 'tsx', 'js', 'jsx', 'json'],
  
  // 模块解析目录
  moduleDirectories: ['node_modules', '<rootDir>/node_modules'],

  // 模块路径别名
  moduleNameMapper: {
    '^@/(.*)$': '<rootDir>/src/$1',
    '^@components/(.*)$': '<rootDir>/src/components/$1',
    '^@pages/(.*)$': '<rootDir>/src/pages/$1',
    '^@hooks/(.*)$': '<rootDir>/src/hooks/$1',
    '^@utils/(.*)$': '<rootDir>/src/utils/$1',
    '^@types/(.*)$': '<rootDir>/src/types/$1',
    '^@visualizations/(.*)$': '<rootDir>/src/visualizations/$1',
    '^@mobile/(.*)$': '<rootDir>/src/mobile/$1',
    '^@stores/(.*)$': '<rootDir>/src/stores/$1',
    '^@api/(.*)$': '<rootDir>/src/api/$1',
    '\\.(css|less|scss|sass)$': 'identity-obj-proxy',
    '\\.(jpg|jpeg|png|gif|webp|svg)$': '<rootDir>/../tests/frontend/__mocks__/fileMock.js'
  },
  
  // 转换器
  transform: {
    '^.+\\.(ts|tsx)$': ['ts-jest', {
      tsconfig: '<rootDir>/tsconfig.json'
    }],
    '^.+\\.(js|jsx)$': 'babel-jest'
  },
  
  // 忽略转换的目录
  transformIgnorePatterns: [
    '/node_modules/(?!(d3|d3-.*|mermaid)/)',
    '\\.pnp\\.[^\\/]+$'
  ],
  
  // 设置文件
  setupFilesAfterEnv: ['<rootDir>/../tests/frontend/setupTests.ts'],
  
  // 覆盖率配置
  collectCoverageFrom: [
    'src/**/*.{ts,tsx}',
    '!src/**/*.d.ts',
    '!src/main.tsx',
    '!src/vite-env.d.ts',
    '!src/**/index.ts'
  ],
  
  coverageThreshold: {
    global: {
      branches: 70,
      functions: 70,
      lines: 70,
      statements: 70
    }
  },
  
  coverageDirectory: '<rootDir>/../tests/coverage/frontend',
  coverageReporters: ['text', 'text-summary', 'lcov', 'html'],
  
  // 搜索根目录
  roots: [
    '<rootDir>',
    '<rootDir>/../tests'
  ],

  // 测试匹配模式
  testMatch: [
    '<rootDir>/../tests/frontend/unit/**/*.test.{ts,tsx}'
  ],
  
  // 测试超时
  testTimeout: 10000,
  
  // 清除mock
  clearMocks: true,
  restoreMocks: true,
  
  // 错误报告
  verbose: true,
  
  // 快照格式
  snapshotFormat: {
    escapeString: true,
    printBasicPrototype: true
  }
};
