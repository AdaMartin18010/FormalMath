import React from 'react';
import { render, screen, fireEvent } from '@testing-library/react';
import { BrowserRouter } from 'react-router-dom';
import Header from '../../../FormalMath-Interactive/src/components/Header';

// Mock组件依赖
jest.mock('lucide-react', () => ({
  Menu: () => <span data-testid="menu-icon">Menu</span>,
  X: () => <span data-testid="close-icon">Close</span>,
  Search: () => <span data-testid="search-icon">Search</span>,
  Bell: () => <span data-testid="bell-icon">Bell</span>,
  User: () => <span data-testid="user-icon">User</span>,
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
    
    expect(screen.getByPlaceholderText('搜索概念...')).toBeInTheDocument();
  });

  it('搜索输入应该响应用户输入', () => {
    renderHeader();
    
    const searchInput = screen.getByPlaceholderText('搜索概念...');
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
    
    expect(screen.getByTestId('mobile-header')).toBeInTheDocument();
  });
});
