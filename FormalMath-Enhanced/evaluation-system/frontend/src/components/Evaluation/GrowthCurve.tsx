import React from 'react';
import {
  LineChart,
  Line,
  XAxis,
  YAxis,
  CartesianGrid,
  Tooltip,
  Legend,
  ResponsiveContainer,
} from 'recharts';
import { TrajectoryPoint } from '../../types';

interface GrowthCurveProps {
  data: TrajectoryPoint[];
  title?: string;
  showAllDimensions?: boolean;
}

const dimensionColors: Record<string, string> = {
  knowledge_mastery: '#4299e1',
  problem_solving: '#48bb78',
  proof_ability: '#ed8936',
  application: '#9f7aea',
  innovation: '#ed64a6',
};

const dimensionNames: Record<string, string> = {
  knowledge_mastery: '知识掌握度',
  problem_solving: '问题解决',
  proof_ability: '证明能力',
  application: '应用能力',
  innovation: '创新思维',
};

const GrowthCurve: React.FC<GrowthCurveProps> = ({
  data,
  title,
  showAllDimensions = true,
}) => {
  // Transform data for the chart
  const chartData = data.map((point) => ({
    date: point.date.split('T')[0],
    period: point.period,
    ...point.scores,
  }));

  const dimensions = showAllDimensions
    ? Object.keys(data[0]?.scores || {})
    : ['weighted_score'];

  return (
    <div className="chart-container">
      {title && <h4 className="chart-title">{title}</h4>}
      <ResponsiveContainer width="100%" height={350}>
        <LineChart data={chartData} margin={{ top: 5, right: 30, left: 20, bottom: 5 }}>
          <CartesianGrid strokeDasharray="3 3" stroke="#e2e8f0" />
          <XAxis
            dataKey="date"
            tick={{ fill: '#4a5568', fontSize: 12 }}
            tickMargin={10}
          />
          <YAxis
            domain={[0, 100]}
            tick={{ fill: '#4a5568', fontSize: 12 }}
            label={{ value: '得分', angle: -90, position: 'insideLeft' }}
          />
          <Tooltip
            content={({ active, payload, label }) => {
              if (active && payload && payload.length) {
                return (
                  <div
                    style={{
                      background: 'white',
                      padding: '12px',
                      border: '1px solid #e2e8f0',
                      borderRadius: '8px',
                      boxShadow: '0 4px 12px rgba(0,0,0,0.1)',
                    }}
                  >
                    <p style={{ margin: '0 0 8px 0', fontWeight: 600, color: '#1a365d' }}>
                      {label}
                    </p>
                    {payload.map((entry: any, index: number) => (
                      <p
                        key={index}
                        style={{
                          margin: '4px 0',
                          color: entry.color,
                          fontSize: '13px',
                        }}
                      >
                        {dimensionNames[entry.dataKey] || entry.name}: {entry.value}分
                      </p>
                    ))}
                  </div>
                );
              }
              return null;
            }}
          />
          <Legend
            formatter={(value: string) => dimensionNames[value] || value}
          />
          {dimensions.map((dim) => (
            <Line
              key={dim}
              type="monotone"
              dataKey={dim}
              stroke={dimensionColors[dim] || '#4299e1'}
              strokeWidth={2}
              dot={{ r: 4, strokeWidth: 2 }}
              activeDot={{ r: 6 }}
            />
          ))}
        </LineChart>
      </ResponsiveContainer>
    </div>
  );
};

export default GrowthCurve;
