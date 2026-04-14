import React from 'react';
import { render, screen, fireEvent } from '@testing-library/react';
import { BrowserRouter } from 'react-router-dom';
import Header from '@components/Header';

// Mock组件依赖
jest.mock('lucide-react', () => ({
  Menu: () => <span data-testid="menu-icon">Menu</span>,
  X: () => <span data-testid="close-icon">Close</span>,
  Search: () => <span data-testid="search-icon">Search</span>,
  Bell: () => <span data-testid="bell-icon">Bell</span>,
  User: () => <span data-testid="user-icon">User</span>,
  Settings: () => <span data-testid="settings-icon">Settings</span>,
  Github: () => <span data-testid="github-icon">GitHub</span>,
  BookOpen: () => <span data-testid="bookopen-icon">BookOpen</span>,
  Network: () => <span data-testid="network-icon">Network</span>,
  GitBranch: () => <span data-testid="gitbranch-icon">GitBranch</span>,
  Brain: () => <span data-testid="brain-icon">Brain</span>,
  BarChart3: () => <span data-testid="barchart3-icon">BarChart3</span>,
  Layout: () => <span data-testid="layout-icon">Layout</span>,
  History: () => <span data-testid="history-icon">History</span>,
  CheckCircle2: () => <span data-testid="checkcircle2-icon">CheckCircle2</span>,
}));

describe('Header组件', () => {
  const mockToggleSidebar = jest.fn();
  
  const renderHeader = (props = {}) => {
    return render(
      <BrowserRouter>
        <Header onToggleSidebar={mockToggleSidebar} {...props} />
      </BrowserRouter>
    );
  };

  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('应该正确渲染Header', () => {
    renderHeader();
    
    expect(screen.getByTestId('header')).toBeInTheDocument();
    expect(screen.getByText('FormalMath')).toBeInTheDocument();
  });

  it('应该渲染菜单按钮', () => {
    renderHeader();
    
    const menuButton = screen.getByTestId('menu-button');
    expect(menuButton).toBeInTheDocument();
  });

  it('点击菜单按钮应该触发回调', () => {
    renderHeader();
    
    const menuButton = screen.getByTestId('menu-button');
    fireEvent.click(menuButton);
    
    expect(mockToggleSidebar).toHaveBeenCalledTimes(1);
  });

  it('应该渲染搜索输入框', () => {
    renderHeader();
    
    // 点击搜索按钮展开搜索栏
    fireEvent.click(screen.getByTitle('搜索'));
    
    expect(screen.getByPlaceholderText('搜索概念、定理、证明...')).toBeInTheDocument();
  });

  it('搜索输入应该响应用户输入', () => {
    renderHeader();
    
    // 点击搜索按钮展开搜索栏
    fireEvent.click(screen.getByTitle('搜索'));
    
    const searchInput = screen.getByPlaceholderText('搜索概念、定理、证明...');
    fireEvent.change(searchInput, { target: { value: '群论' } });
    
    expect(searchInput).toHaveValue('群论');
  });

  it('应该响应式适配移动端', () => {
    // 模拟移动端视口
    window.matchMedia = jest.fn().mockImplementation(query => ({
      matches: query === '(max-width: 768px)',
      media: query,
      onchange: null,
      addListener: jest.fn(),
      removeListener: jest.fn(),
      addEventListener: jest.fn(),
      removeEventListener: jest.fn(),
      dispatchEvent: jest.fn(),
    }));
    
    renderHeader();
    
    // 点击菜单按钮展开移动端导航
    fireEvent.click(screen.getByTestId('menu-button'));
    
    expect(screen.getByTestId('mobile-header')).toBeInTheDocument();
  });
});
