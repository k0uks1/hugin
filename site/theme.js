// The theme switch (light or dark), inlined into the <head> of every page by site/build.mjs so that the
// page never renders in the wrong theme. Without a choice the page follows the system setting (the CSS
// media query); the button in the header (.theme) stores the choice as `data-theme` on <html> and in
// localStorage, and sets the reference's mdBook theme to match (light or navy).
(function () {
  var root = document.documentElement, key = "hugin-theme";
  try {
    var t = localStorage.getItem(key);
    if (t === "light" || t === "dark") root.setAttribute("data-theme", t);
  } catch (e) {}
  document.addEventListener("click", function (e) {
    if (!e.target.closest || !e.target.closest(".theme")) return;
    var now = root.getAttribute("data-theme") ||
      (matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light");
    var next = now === "dark" ? "light" : "dark";
    root.setAttribute("data-theme", next);
    try {
      localStorage.setItem(key, next);
      localStorage.setItem("mdbook-theme", next === "dark" ? "navy" : "light");
    } catch (e) {}
  });
})();
