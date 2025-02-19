var sig File {}
var sig Trash in File {}

fact init {
  no Trash
}

pred empty {
  some Trash and       // guard
  after no Trash   // effect on Trash
  File' = File + Trash // effect on File
}

pred delete [f : File] {
  not (f in Trash)   // guard
  Trash' = Trash + f // effect on Trash
  File' = File       // frame condition on File
}

pred permanently_delete [f : File] {
  f in Trash    // Only delete files in trash
  Trash' = Trash - f // Remove file from Trash
  File' = File - f // Remove file from File
}

pred restore [f : File] {
  f in Trash         // guard
  Trash' = Trash - f // effect on Trash
  File' = File       // frame condition on File
}

fact trans {
  always (empty or (some f : File | delete[f] or restore[f]))
}

run example {}
