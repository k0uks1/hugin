// The Hugin extension: starts `hugin lsp` and connects VS Code to it over stdio. Highlighting comes from
// the TextMate grammar alone, so it works without the server.
//
// The meta level (issue #54): inlay hints are configured by `hugin.inlayHints.*` (sent as initialization
// options and on every change), and `Hugin: Show Expansion` (also the code lenses on directive and
// functor applications) opens the staged result of the meta code at the cursor in a read-only document
// `hugin-expansion:`, asking the server with its command `hugin.expansion`.
const vscode = require("vscode");
const { LanguageClient } = require("vscode-languageclient/node");

let client;

const scheme = "hugin-expansion";
const expansions = new Map(); // URI of an expansion document -> its text
const changed = new vscode.EventEmitter();

function hintSettings() {
  const c = vscode.workspace.getConfiguration("hugin.inlayHints");
  return { staging: c.get("staging", true), implicits: c.get("implicits", true), levels: c.get("levels", false) };
}

/** Shows the expansion at a position: the arguments of a code lens (uri, line, character), or the cursor. */
async function showExpansion(uri, line, character) {
  if (uri === undefined) {
    const editor = vscode.window.activeTextEditor;
    if (!editor || editor.document.languageId !== "hugin") return;
    uri = editor.document.uri.toString();
    line = editor.selection.active.line;
    character = editor.selection.active.character;
  }
  const text = await client.sendRequest("workspace/executeCommand", { command: "hugin.expansion", arguments: [uri, line, character] });
  if (!text) {
    vscode.window.showInformationMessage("No staged code here: put the cursor on a directive, a functor application or an object item.");
    return;
  }
  const name = vscode.Uri.parse(uri).path.split("/").pop();
  const doc = vscode.Uri.from({ scheme, path: `/${name}.expansion.hgn`, query: `${line}:${character}` });
  expansions.set(doc.toString(), text);
  changed.fire(doc);
  const shown = await vscode.workspace.openTextDocument(doc);
  await vscode.languages.setTextDocumentLanguage(shown, "hugin");
  await vscode.window.showTextDocument(shown, { preview: true, viewColumn: vscode.ViewColumn.Beside });
}

function activate(context) {
  const command = vscode.workspace.getConfiguration("hugin").get("server.path", "hugin");
  const serverOptions = { command, args: ["lsp"] };
  const clientOptions = {
    documentSelector: [{ scheme: "file", language: "hugin" }, { scheme: "untitled", language: "hugin" }],
    // edits of imported files made outside the editor reach the server
    synchronize: { fileEvents: vscode.workspace.createFileSystemWatcher("**/*.{hgn,facts}") },
    initializationOptions: { inlayHints: hintSettings() },
  };
  client = new LanguageClient("hugin", "Hugin", serverOptions, clientOptions);
  client.start().catch((e) =>
    vscode.window.showErrorMessage(`Could not start the Hugin language server (\`${command} lsp\`): ${e.message ?? e}`)
  );
  context.subscriptions.push(
    vscode.workspace.registerTextDocumentContentProvider(scheme, {
      onDidChange: changed.event,
      provideTextDocumentContent: (uri) => expansions.get(uri.toString()) ?? "",
    }),
    vscode.commands.registerCommand("hugin.showExpansion", showExpansion),
    vscode.workspace.onDidChangeConfiguration((e) => {
      if (e.affectsConfiguration("hugin.server.path")) {
        vscode.window.showInformationMessage("Reload the window to restart the Hugin language server.");
      }
      if (e.affectsConfiguration("hugin.inlayHints")) {
        client.sendNotification("workspace/didChangeConfiguration", { settings: { hugin: { inlayHints: hintSettings() } } });
      }
    })
  );
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
