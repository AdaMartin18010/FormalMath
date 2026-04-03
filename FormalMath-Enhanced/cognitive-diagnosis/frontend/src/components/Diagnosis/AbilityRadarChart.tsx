import React from 'react';
import {
  Chart as ChartJS,
  RadialLinearScale,
  PointElement,
  LineElement,
  Filler,
  Tooltip,
  Legend
} from 'chart.js';
import { Radar } from 'react-chartjs-2';

ChartJS.register(
  RadialLinearScale,
  PointElement,
  LineElement,
  Filler,
  Tooltip,
  Legend
);

interface AbilityRadarChartProps {
  data: {
    labels: string[];
    datasets: any[];
  };
}

const AbilityRadarChart: React.FC<AbilityRadarChartProps> = ({ data }) => {
  const defaultData = {
    labels: ['L0-基础', 'L1-中级', 'L2-高级', 'L3-研究'],
    datasets: [
      {
        label: '能力水平',
        data: [70, 60, 45, 20],
        backgroundColor: 'rgba(25, 118, 210, 0.2)',
        borderColor: 'rgba(25, 118, 210, 1)',
        borderWidth: 2,
        pointBackgroundColor: 'rgba(25, 118, 210, 1)',
      }
    ]
  };

  const chartData = data || defaultData;

  const options = {
    responsive: true,
    maintainAspectRatio: true,
    scales: {
      r: {
        beginAtZero: true,
        max: 100,
        min: 0,
        ticks: {
          stepSize: 20,
          font: {
            size: 11
          }
        },
        pointLabels: {
          font: {
            size: 12,
            weight: 'bold' as const
          }
        }
      }
    },
    plugins: {
      legend: {
        display: false
      },
      tooltip: {
        callbacks: {
          label: function(context: any) {
            return `掌握度: ${context.raw}%`;
          }
        }
      }
    }
  };

  return <Radar data={chartData} options={options} />;
};

export default AbilityRadarChart;
