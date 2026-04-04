/**
 * API集成测试
 * 测试前后端API交互
 */

import { describe, it, expect, beforeAll, afterAll } from '@jest/globals';
import { spawn } from 'child_process';
import { setTimeout } from 'timers/promises';

const API_BASE_URL = process.env.API_URL || 'http://localhost:8000';
const FRONTEND_URL = process.env.FRONTEND_URL || 'http://localhost:3000';

describe('API集成测试', () => {
  
  describe('概念API', () => {
    it('应该能够获取概念列表', async () => {
      const response = await fetch(`${API_BASE_URL}/api/concepts`);
      expect(response.status).toBe(200);
      
      const data = await response.json();
      expect(Array.isArray(data)).toBe(true);
    });

    it('应该能够搜索概念', async () => {
      const query = '群论';
      const response = await fetch(
        `${API_BASE_URL}/api/concepts/search?q=${encodeURIComponent(query)}`
      );
      expect(response.status).toBe(200);
      
      const data = await response.json();
      expect(data).toHaveProperty('results');
      expect(Array.isArray(data.results)).toBe(true);
    });

    it('应该能够获取单个概念详情', async () => {
      const conceptId = 'group_theory';
      const response = await fetch(`${API_BASE_URL}/api/concepts/${conceptId}`);
      
      if (response.status === 200) {
        const data = await response.json();
        expect(data).toHaveProperty('id');
        expect(data).toHaveProperty('name');
      } else {
        expect(response.status).toBe(404);
      }
    });
  });

  describe('图谱API', () => {
    it('应该能够获取图谱数据', async () => {
      const response = await fetch(`${API_BASE_URL}/api/graph`);
      expect(response.status).toBe(200);
      
      const data = await response.json();
      expect(data).toHaveProperty('nodes');
      expect(data).toHaveProperty('edges');
      expect(Array.isArray(data.nodes)).toBe(true);
      expect(Array.isArray(data.edges)).toBe(true);
    });

    it('应该能够获取学习路径', async () => {
      const start = 'set_theory';
      const goal = 'group_theory';
      
      const response = await fetch(
        `${API_BASE_URL}/api/graph/path?start=${start}&goal=${goal}`
      );
      
      expect(response.status).toBe(200);
      
      const data = await response.json();
      expect(data).toHaveProperty('path');
      expect(Array.isArray(data.path)).toBe(true);
    });
  });

  describe('AI助手API', () => {
    it('应该能够发送聊天消息', async () => {
      const message = {
        content: '什么是群论？',
        sessionId: 'test-session-123'
      };
      
      const response = await fetch(`${API_BASE_URL}/api/chat`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json'
        },
        body: JSON.stringify(message)
      });
      
      expect(response.status).toBe(200);
      
      const data = await response.json();
      expect(data).toHaveProperty('response');
      expect(typeof data.response).toBe('string');
    }, 30000); // 30秒超时
  });

  describe('用户API', () => {
    it('应该能够用户注册', async () => {
      const user = {
        email: `test_${Date.now()}@example.com`,
        password: 'TestPassword123',
        name: 'Test User'
      };
      
      const response = await fetch(`${API_BASE_URL}/api/auth/register`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json'
        },
        body: JSON.stringify(user)
      });
      
      // 可能返回201(创建成功)或409(已存在)
      expect([201, 409]).toContain(response.status);
    });

    it('应该能够用户登录', async () => {
      const credentials = {
        email: 'test@example.com',
        password: 'TestPassword123'
      };
      
      const response = await fetch(`${API_BASE_URL}/api/auth/login`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json'
        },
        body: JSON.stringify(credentials)
      });
      
      // 可能返回200(成功)或401(未授权)
      expect([200, 401]).toContain(response.status);
    });
  });
});

describe('端到端工作流测试', () => {
  it('完整的学习路径工作流', async () => {
    // 1. 获取概念列表
    const conceptsResponse = await fetch(`${API_BASE_URL}/api/concepts?limit=5`);
    expect(conceptsResponse.status).toBe(200);
    const concepts = await conceptsResponse.json();
    
    if (concepts.length >= 2) {
      const start = concepts[0].id;
      const goal = concepts[concepts.length - 1].id;
      
      // 2. 获取学习路径
      const pathResponse = await fetch(
        `${API_BASE_URL}/api/graph/path?start=${start}&goal=${goal}`
      );
      expect(pathResponse.status).toBe(200);
      
      const pathData = await pathResponse.json();
      expect(pathData).toHaveProperty('path');
      
      // 3. 获取路径上每个概念的详情
      for (const conceptId of pathData.path.slice(0, 3)) {
        const detailResponse = await fetch(
          `${API_BASE_URL}/api/concepts/${conceptId}`
        );
        expect(detailResponse.status).toBe(200);
      }
    }
  });
});
