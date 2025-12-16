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

resource "aws_iam_instance_profile" "ssm_profile" {
  name = "rtlmeter-bench-ssm-profile"
  role = aws_iam_role.ssm_role.name
}

# Look up default VPC
data "aws_vpc" "default" {
  default = true
}

# Look up subnet in the specified availability zone
data "aws_subnet" "selected" {
  vpc_id            = data.aws_vpc.default.id
  availability_zone = var.availability_zone
  default_for_az    = true
}

# Spot EC2 instance
resource "aws_instance" "benchmark" {
  ami                  = var.ami_id
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
