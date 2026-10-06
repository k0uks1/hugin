// The Hugin extension: starts `hugin lsp` and connects VS Code to it over stdio. Highlighting comes from
// the TextMate grammar alone, so it works without the server.
const vscode = require("vscode");
const { LanguageClient } = require("vscode-languageclient/node");

let client;

function activate(context) {
  const command = vscode.workspace.getConfiguration("hugin").get("server.path", "hugin");
  const serverOptions = { command, args: ["lsp"] };
  const clientOptions = {
    documentSelector: [{ language: "hugin" }],
    // edits of imported files made outside the editor reach the server
    synchronize: { fileEvents: vscode.workspace.createFileSystemWatcher("**/*.{hgn,facts}") },
  };
  client = new LanguageClient("hugin", "Hugin", serverOptions, clientOptions);
  client.start().catch((e) =>
    vscode.window.showErrorMessage(`Could not start the Hugin language server (\`${command} lsp\`): ${e.message ?? e}`)
  );
  context.subscriptions.push(
    vscode.workspace.onDidChangeConfiguration((e) => {
      if (e.affectsConfiguration("hugin.server.path")) {
        vscode.window.showInformationMessage("Reload the window to restart the Hugin language server.");
      }
    })
  );
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
