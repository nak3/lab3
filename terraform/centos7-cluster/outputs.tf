output "resource_group" {
  value = "${var.resource_group}"
}

output "fqdn" {
  value = "${azurerm_public_ip.pip.fqdn}"
}

output "ip_address" {
  value = "${azurerm_public_ip.pip.ip_address}"
}

output "ssh_command_vm1" {
  value = "ssh ${var.vm_admin_username}@${azurerm_public_ip.pip.ip_address} -p 64001"
}

output "ssh_command_vm2" {
  value = "ssh ${var.vm_admin_username}@${azurerm_public_ip.pip.ip_address} -p 64002"
}
