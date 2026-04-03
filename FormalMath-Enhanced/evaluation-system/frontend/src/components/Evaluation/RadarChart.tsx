import React from 'react';
import {
  Radar,
  RadarChart,
  PolarGrid,
  PolarAngleAxis,
  PolarRadiusAxis,
  ResponsiveContainer,
  Tooltip,
  Legend,
} from 'recharts';

interface RadarDataPoint {
  dimension: string;
  score: number;
  fullMark: number;
}

interface RadarChartProps {
  data: RadarDataPoint[];
  title?: string;
  comparisonData?: RadarDataPoint[];
  showLegend?: boolean;
}

const RadarChartComponent: React.FC<RadarChartProps> = ({
  data,
  title,
  comparisonData,
  showLegend = true,
}) => {
  // Merge data if comparison exists
  const chartData = comparisonData
    ? data.map((item, index) => ({
        dimension: item.dimension,
        current: item.score,
        comparison: comparisonData[index]?.score || 0,
        fullMark: 100,
      }))
    : data.map((item) => ({
        dimension: item.dimension,
        score: item.score,
        fullMark: 100,
      }));

  return (
    <div className="chart-container">
      {title && <h4 className="chart-title">{title}</h4>}
      <ResponsiveContainer width="100%" height={350}>
        <RadarChart cx="50%" cy="50%" outerRadius="70%" data={chartData}>
          <PolarGrid stroke="#e2e8f0" />
          <PolarAngleAxis
            dataKey="dimension"
            tick={{ fill: '#4a5568', fontSize: 12 }}
          />
          <PolarRadiusAxis
            angle={90}
            domain={[0, 100]}
            tick={{ fill: '#a0aec0', fontSize: 10 }}
            tickCount={6}
          />
          <Tooltip
            content={({ active, payload }) => {
              if (active && payload && payload.length) {
                return (
                  <div
                    style={{
                      background: 'white',
                      padding: '10px',
                      border: '1px solid #e2e8f0',
                      borderRadius: '4px',
                      boxShadow: '0 2px 8px rgba(0,0,0,0.1)',
                    }}
                  >
                    <p
                      style={{ margin: 0, fontWeight: 600, color: '#1a365d' }}
                    >
                      {payload[0].payload.dimension}
                    </p>
                    {payload.map((entry: any, index: number) => (
                      <p
                        key={index}
                        style={{
                          margin: '4px 0 0 0',
                          color: entry.color,
                          fontSize: '14px',
                        }}
                      >
                        {entry.name}: {entry.value}分
                      </p>
                    ))}
                  </div>
                );
              }
              return null;
            }}
          />
          {comparisonData ? (
            <>
              <Radar
                name="当前得分"
                dataKey="current"
                stroke="#4299e1"
                fill="#4299e1"
                fillOpacity={0.3}
                strokeWidth={2}
              />
              <Radar
                name="对比基准"
                dataKey="comparison"
                stroke="#48bb78"
                fill="#48bb78"
                fillOpacity={0.2}
                strokeWidth={2}
                strokeDasharray="5 5"
              />
            </>
          ) : (
            <Radar
              name="得分"
              dataKey="score"
              stroke="#4299e1"
              fill="#4299e1"
              fillOpacity={0.4}
              strokeWidth={2}
            />
          )}
          {showLegend && <Legend />}
        </RadarChart>
      </ResponsiveContainer>
    </div>
  );
};

export default RadarChartComponent;
