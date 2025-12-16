output "instance_id" {
  description = "EC2 instance ID for SSM commands"
  value       = aws_instance.benchmark.id
}

output "public_ip" {
  description = "Public IP address (if assigned)"
  value       = aws_instance.benchmark.public_ip
}

output "private_ip" {
  description = "Private IP address"
  value       = aws_instance.benchmark.private_ip
}

output "s3_bucket" {
  description = "S3 bucket for results backup"
  value       = aws_s3_bucket.results.bucket
}
