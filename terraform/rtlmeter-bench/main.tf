terraform {
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 5.0"
    }
  }
}

provider "aws" {
  region = var.aws_region
}

# Find AZs where the instance type is available
data "aws_ec2_instance_type_offerings" "available" {
  filter {
    name   = "instance-type"
    values = [var.instance_type]
  }

  location_type = "availability-zone"
}

locals {
  # Use explicit AZ if provided, otherwise pick first available AZ for the instance type
  availability_zone = var.availability_zone != "" ? var.availability_zone : sort(data.aws_ec2_instance_type_offerings.available.locations)[0]
}

# IAM role for SSM access
resource "aws_iam_role" "ssm_role" {
  name = "rtlmeter-bench-ssm-role"

  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Action = "sts:AssumeRole"
        Effect = "Allow"
        Principal = {
          Service = "ec2.amazonaws.com"
        }
      }
    ]
  })
}

resource "aws_iam_role_policy_attachment" "ssm_policy" {
  role       = aws_iam_role.ssm_role.name
  policy_arn = "arn:aws:iam::aws:policy/AmazonSSMManagedInstanceCore"
}

# CloudWatch agent needs permissions to publish metrics
resource "aws_iam_role_policy_attachment" "cloudwatch_agent_policy" {
  role       = aws_iam_role.ssm_role.name
  policy_arn = "arn:aws:iam::aws:policy/CloudWatchAgentServerPolicy"
}

# S3 bucket for results backup
resource "aws_s3_bucket" "results" {
  bucket_prefix = "rtlmeter-results-"
  force_destroy = true
}

resource "aws_s3_bucket_lifecycle_configuration" "results" {
  bucket = aws_s3_bucket.results.id

  rule {
    id     = "expire-old-results"
    status = "Enabled"

    filter {} # Apply to all objects

    expiration {
      days = 90
    }
  }
}

# Allow EC2 to write to S3
resource "aws_iam_role_policy" "s3_write" {
  name = "rtlmeter-s3-write"
  role = aws_iam_role.ssm_role.id

  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Effect = "Allow"
        Action = [
          "s3:PutObject",
          "s3:GetObject",
          "s3:ListBucket"
        ]
        Resource = [
          aws_s3_bucket.results.arn,
          "${aws_s3_bucket.results.arn}/*"
        ]
      }
    ]
  })
}

resource "aws_iam_instance_profile" "ssm_profile" {
  name = "rtlmeter-bench-ssm-profile"
  role = aws_iam_role.ssm_role.name
}

# Look up latest Ubuntu 24.04 AMI
data "aws_ami" "ubuntu" {
  most_recent = true
  owners      = ["099720109477"] # Canonical

  filter {
    name   = "name"
    values = ["ubuntu/images/hvm-ssd-gp3/ubuntu-noble-24.04-amd64-server-*"]
  }

  filter {
    name   = "virtualization-type"
    values = ["hvm"]
  }

  filter {
    name   = "architecture"
    values = ["x86_64"]
  }
}

# Look up default VPC
data "aws_vpc" "default" {
  default = true
}

# Look up subnet in the specified availability zone
data "aws_subnet" "selected" {
  vpc_id            = data.aws_vpc.default.id
  availability_zone = local.availability_zone
  default_for_az    = true
}

# CloudWatch Dashboard for monitoring
resource "aws_cloudwatch_dashboard" "benchmark" {
  dashboard_name = "RTLMeter-Benchmark"

  dashboard_body = jsonencode({
    widgets = [
      {
        type   = "metric"
        x      = 0
        y      = 0
        width  = 12
        height = 6
        properties = {
          title  = "CPU Utilization"
          region = var.aws_region
          metrics = [
            ["AWS/EC2", "CPUUtilization", "InstanceId", aws_instance.benchmark.id]
          ]
          period = 60
          stat   = "Average"
        }
      },
      {
        type   = "metric"
        x      = 12
        y      = 0
        width  = 12
        height = 6
        properties = {
          title  = "Memory Used %"
          region = var.aws_region
          metrics = [
            ["RTLMeter", "mem_used_percent", "InstanceId", aws_instance.benchmark.id]
          ]
          period = 60
          stat   = "Average"
        }
      },
      {
        type   = "metric"
        x      = 0
        y      = 6
        width  = 12
        height = 6
        properties = {
          title  = "Disk Used %"
          region = var.aws_region
          metrics = [
            ["RTLMeter", "disk_used_percent", "InstanceId", aws_instance.benchmark.id, "path", "/", "fstype", "ext4"]
          ]
          period = 60
          stat   = "Average"
        }
      },
      {
        type   = "metric"
        x      = 12
        y      = 6
        width  = 12
        height = 6
        properties = {
          title  = "Network I/O"
          region = var.aws_region
          metrics = [
            ["AWS/EC2", "NetworkIn", "InstanceId", aws_instance.benchmark.id],
            ["AWS/EC2", "NetworkOut", "InstanceId", aws_instance.benchmark.id]
          ]
          period = 60
          stat   = "Sum"
        }
      },
      {
        type   = "metric"
        x      = 0
        y      = 12
        width  = 12
        height = 6
        properties = {
          title  = "Disk I/O (bytes)"
          region = var.aws_region
          metrics = [
            ["RTLMeter", "diskio_read_bytes", "InstanceId", aws_instance.benchmark.id],
            ["RTLMeter", "diskio_write_bytes", "InstanceId", aws_instance.benchmark.id]
          ]
          period = 60
          stat   = "Sum"
        }
      },
      {
        type   = "metric"
        x      = 12
        y      = 12
        width  = 12
        height = 6
        properties = {
          title  = "Disk I/O (ops)"
          region = var.aws_region
          metrics = [
            ["RTLMeter", "diskio_reads", "InstanceId", aws_instance.benchmark.id],
            ["RTLMeter", "diskio_writes", "InstanceId", aws_instance.benchmark.id]
          ]
          period = 60
          stat   = "Sum"
        }
      }
    ]
  })
}

# Spot EC2 instance
resource "aws_instance" "benchmark" {
  ami                  = data.aws_ami.ubuntu.id
  instance_type        = var.instance_type
  iam_instance_profile = aws_iam_instance_profile.ssm_profile.name
  availability_zone    = var.availability_zone
  subnet_id            = data.aws_subnet.selected.id

  instance_market_options {
    market_type = "spot"
    spot_options {
      spot_instance_type = "one-time"
    }
  }

  # Storage
  root_block_device {
    volume_size = var.root_volume_size
    volume_type = "gp3"
    throughput  = 250
    iops        = 3000
  }

  tags = {
    Name = "rtlmeter-benchmark"
  }
}
