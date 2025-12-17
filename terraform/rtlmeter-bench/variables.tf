variable "aws_region" {
  description = "AWS region"
  type        = string
  default     = "us-east-2"
}

variable "instance_type" {
  description = "EC2 instance type"
  type        = string
  default     = "c8i.metal-48xl" # 192 vCPUs (96 physical cores), 384GB RAM - bare metal
}

variable "availability_zone" {
  description = "Availability zone (defaults to region + 'a')"
  type        = string
  default     = "" # Empty means derive from region
}

variable "root_volume_size" {
  description = "Root volume size in GB"
  type        = number
  default     = 200 # Extra headroom for long benchmarks
}
